import os, json, time, sqlite3, threading, secrets, re, uuid, shutil
from datetime import datetime, timedelta
from functools import wraps
from html import escape
from zoneinfo import ZoneInfo
import requests, base64, hmac, hashlib, struct
from bs4 import BeautifulSoup
from flask import Flask, render_template, request, redirect, url_for, session, flash, jsonify, g
from werkzeug.security import generate_password_hash, check_password_hash

WIB=ZoneInfo('Asia/Jakarta')
DURATIONS={'makan':20,'merokok':10,'toilet':5,'bab':15}
MAX_ACTIVE_LEAVES=5
POLICY_VERSION=os.getenv('POLICY_VERSION','2026-08-07-v1')

def resolve_db_path():
    raw=(os.getenv('DB_PATH') or '').strip(); data_dir=(os.getenv('DATA_DIR') or '/data').strip() or '/data'
    if not raw: raw=os.path.join(data_dir,'omtogel_staff.db')
    raw=os.path.abspath(os.path.expanduser(raw))
    if raw.endswith(os.sep) or os.path.isdir(raw): raw=os.path.join(raw,'omtogel_staff.db')
    # recover from old accidental nested DB_PATH=/data/omtogel_staff.db when it already became a folder
    if os.path.isdir(raw): raw=os.path.join(raw,'omtogel_staff.db')
    parent=os.path.dirname(raw) or '.'; os.makedirs(parent,exist_ok=True)
    return raw
DB_PATH=resolve_db_path()
BOT_TOKEN=os.getenv('BOT_TOKEN','').strip(); INOUT_CHAT_ID=os.getenv('INOUT_CHAT_ID',os.getenv('CHAT_ID','')).strip(); ALERT_CHAT_ID=os.getenv('ALERT_CHAT_ID',os.getenv('CHAT_ID','')).strip(); API_KEY=os.getenv('API_KEY','').strip()
INOUT_ADMIN_IDS=[x.strip() for x in os.getenv('INOUT_ADMIN_IDS','').split(',') if x.strip()]
LATE_MINUTES=int(os.getenv('LATE_MINUTES','5')); SCAN_SECONDS=int(os.getenv('SCAN_SECONDS','5')); LEADER_TTL_SECONDS=int(os.getenv('LEADER_TTL_SECONDS','15')); MAX_DEVICES=int(os.getenv('MAX_DEVICES','0'))
RETENTION_DAYS=max(1,int(os.getenv('RETENTION_DAYS','60')))
ADMIN_USERNAME=os.getenv('ADMIN_USERNAME','admin'); ADMIN_PASSWORD=os.getenv('ADMIN_PASSWORD','admin12345'); SECRET_KEY=os.getenv('SECRET_KEY',secrets.token_hex(32))
app=Flask(__name__); app.secret_key=SECRET_KEY; app.config.update(SESSION_COOKIE_HTTPONLY=True,SESSION_COOKIE_SAMESITE='Lax')

@app.template_filter('fmt_wib')
def fmt_wib(value):
    if not value:
        return '-'
    try:
        dt=datetime.fromisoformat(str(value))
        if dt.tzinfo is None:
            dt=dt.replace(tzinfo=WIB)
        else:
            dt=dt.astimezone(WIB)
        months=['Januari','Februari','Maret','April','Mei','Juni','Juli','Agustus','September','Oktober','November','Desember']
        return f"{dt.day:02d} {months[dt.month-1]} {dt.year} • {dt.strftime('%H:%M:%S')} WIB"
    except Exception:
        return str(value)
@app.template_filter('fmt_duration')
def fmt_duration_seconds(value):
    if value is None:
        return '-'
    try:
        total=max(0,int(float(value)))
        h,rem=divmod(total,3600); m,sec=divmod(rem,60)
        if h: return f"{h} jam {m} menit {sec} detik"
        return f"{m} menit {sec} detik"
    except Exception:
        return '-'

def leave_duration_seconds(row, end_time=None):
    try:
        start=datetime.fromisoformat(row['out_at'])
        end=datetime.fromisoformat(row['in_at']) if row['in_at'] else (end_time or now())
        return max(0,int((end-start).total_seconds()))
    except Exception:
        return 0

lock=threading.RLock(); bg_started=False

def now(): return datetime.now(WIB)
def totp_code(secret, for_time=None):
    for_time = int(for_time or time.time())
    padded = secret + '=' * ((8 - len(secret) % 8) % 8)
    key = base64.b32decode(padded, casefold=True)
    msg = struct.pack('>Q', for_time // 30)
    digest = hmac.new(key, msg, hashlib.sha1).digest()
    off = digest[-1] & 0x0F
    val = (struct.unpack('>I', digest[off:off+4])[0] & 0x7fffffff) % 1000000
    return f'{val:06d}'

def totp_verify(secret, code):
    if not secret or not re.fullmatch(r'\d{6}', code or ''): return False
    t=int(time.time())
    return any(hmac.compare_digest(totp_code(secret,t+(i*30)),code) for i in (-1,0,1))

def db_conn():
    c=sqlite3.connect(DB_PATH,timeout=30,check_same_thread=False); c.row_factory=sqlite3.Row
    c.execute('PRAGMA journal_mode=WAL'); c.execute('PRAGMA foreign_keys=ON'); c.execute('PRAGMA busy_timeout=30000'); return c

def addcol(c,table,name,decl):
    cols={r['name'] for r in c.execute(f'PRAGMA table_info({table})')}
    if name not in cols: c.execute(f'ALTER TABLE {table} ADD COLUMN {name} {decl}')

def migrate_global_shifts(c):
    """Gabungkan shift lama per-kantor menjadi satu Master Shift global.

    Kolom office_id dipertahankan untuk kompatibilitas database lama, tetapi semua
    shift versi baru selalu office_id=NULL. Referensi assignment/schedule lama
    dipindahkan ke shift global agar riwayat tidak putus.
    """
    rows=c.execute("SELECT * FROM shifts ORDER BY id").fetchall()
    groups={}
    for r in rows:
        key=(r['name'] or '').strip().casefold()
        if key:
            groups.setdefault(key,[]).append(r)
    for key,items in groups.items():
        global_items=[r for r in items if r['office_id'] is None]
        if global_items:
            canonical=global_items[0]
            canonical_id=canonical['id']
        else:
            src=next((r for r in items if (r['status'] or 'Aktif')=='Aktif'),items[0])
            canonical_id=c.execute(
                "INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(NULL,?,?,?,?,?)",
                ((src['name'] or '').strip(),src['code'] or '',src['start_time'] or '00:00',src['end_time'] or '00:00',src['status'] or 'Aktif')
            ).lastrowid
        # Pindahkan semua referensi dari duplikat lama ke shift global.
        for r in items:
            if r['id']==canonical_id:
                continue
            c.execute('UPDATE shift_schedules SET shift_id=? WHERE shift_id=?',(canonical_id,r['id']))
            c.execute('UPDATE assignments SET shift_id=? WHERE shift_id=?',(canonical_id,r['id']))
            c.execute('DELETE FROM shifts WHERE id=?',(r['id'],))
        c.execute('UPDATE shifts SET office_id=NULL,name=TRIM(name) WHERE id=?',(canonical_id,))
    # Bersihkan kemungkinan duplikat global lama (NULL tidak dibatasi UNIQUE SQLite).
    globals_=c.execute("SELECT * FROM shifts WHERE office_id IS NULL ORDER BY id").fetchall()
    seen={}
    for r in globals_:
        key=(r['name'] or '').strip().casefold()
        if not key: continue
        if key not in seen:
            seen[key]=r['id']; continue
        keep=seen[key]
        c.execute('UPDATE shift_schedules SET shift_id=? WHERE shift_id=?',(keep,r['id']))
        c.execute('UPDATE assignments SET shift_id=? WHERE shift_id=?',(keep,r['id']))
        c.execute('DELETE FROM shifts WHERE id=?',(r['id'],))
    c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_shifts_global_name ON shifts(lower(name)) WHERE office_id IS NULL")

def init_db():
  with lock,db_conn() as c:
    c.executescript('''
    CREATE TABLE IF NOT EXISTS offices(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT UNIQUE NOT NULL,location TEXT,status TEXT DEFAULT 'Aktif');
    CREATE TABLE IF NOT EXISTS staff(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT NOT NULL,telegram_id TEXT UNIQUE,telegram_username TEXT,email TEXT,agent_code TEXT,cs_name TEXT,office_id INTEGER,position TEXT DEFAULT 'CS',status TEXT DEFAULT 'Aktif',join_date TEXT,exit_date TEXT,exit_reason TEXT,notes TEXT,FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY AUTOINCREMENT,username TEXT UNIQUE NOT NULL,password_hash TEXT NOT NULL,role TEXT DEFAULT 'staff',staff_id INTEGER UNIQUE,office_id INTEGER,is_active INTEGER DEFAULT 1,must_change_password INTEGER DEFAULT 1,allowed_menus TEXT DEFAULT '["my_dashboard","inout","nawala","mistakes","history","account"]',device_token TEXT,last_login TEXT,twofa_secret TEXT,twofa_enabled INTEGER DEFAULT 0,FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS shifts(id INTEGER PRIMARY KEY AUTOINCREMENT,office_id INTEGER,name TEXT NOT NULL,code TEXT,start_time TEXT,end_time TEXT,status TEXT DEFAULT 'Aktif',FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS shift_schedules(id INTEGER PRIMARY KEY AUTOINCREMENT,work_date TEXT NOT NULL,staff_id INTEGER NOT NULL,shift_id INTEGER NOT NULL,office_id INTEGER NOT NULL,UNIQUE(work_date,staff_id),FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(shift_id) REFERENCES shifts(id),FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS channels(id INTEGER PRIMARY KEY AUTOINCREMENT,office_id INTEGER,name TEXT NOT NULL,category TEXT NOT NULL,aliases TEXT DEFAULT '',status TEXT DEFAULT 'Aktif',UNIQUE(office_id,name),FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS assignments(id INTEGER PRIMARY KEY AUTOINCREMENT,assignment_batch_id TEXT,work_date TEXT NOT NULL,office_id INTEGER,shift_id INTEGER,staff_id INTEGER,channel_id INTEGER,category TEXT,target TEXT,start_time TEXT,end_time TEXT,is_active INTEGER DEFAULT 1,FOREIGN KEY(office_id) REFERENCES offices(id),FOREIGN KEY(shift_id) REFERENCES shifts(id),FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(channel_id) REFERENCES channels(id));
    CREATE TABLE IF NOT EXISTS offdays(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,off_date TEXT,notes TEXT,created_at TEXT,UNIQUE(staff_id,off_date),FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS leaves(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER NOT NULL,reason TEXT,out_at TEXT,expected_at TEXT,in_at TEXT,status TEXT DEFAULT 'OUT',late_minutes INTEGER DEFAULT 0,fine INTEGER DEFAULT 0,source TEXT,notified_overdue INTEGER DEFAULT 0,assignment_snapshot TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS warnings(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,type TEXT,warning_date TEXT,reason TEXT,fine INTEGER DEFAULT 0,notes TEXT,created_by INTEGER,created_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS memos(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,title TEXT,category TEXT,body TEXT,priority TEXT DEFAULT 'Normal',status TEXT DEFAULT 'Baru',leader_reply TEXT,created_at TEXT,updated_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS devices(device_id TEXT PRIMARY KEY,device_name TEXT,office_id INTEGER,last_seen INTEGER,page_url TEXT,form_count INTEGER DEFAULT 0,late_count INTEGER DEFAULT 0,FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS deposit_forms(id INTEGER PRIMARY KEY AUTOINCREMENT,form_id TEXT UNIQUE,device_id TEXT,office_id INTEGER,username TEXT,game_id TEXT,destination TEXT,destination_account TEXT,destination_owner TEXT,form_time TEXT,amount TEXT,bank TEXT,first_seen INTEGER,last_seen INTEGER,status TEXT DEFAULT 'pending',alert_sent INTEGER DEFAULT 0,staff_id INTEGER,assignment_id INTEGER,staff_status TEXT,processed_at TEXT,staff_name_snapshot TEXT,cs_name_snapshot TEXT,jobdesk_snapshot TEXT,office_snapshot TEXT,age_at_alert INTEGER DEFAULT 0,alerted_at TEXT,mapping_status TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS audit_logs(id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER,action TEXT,detail TEXT,created_at TEXT);
    CREATE TABLE IF NOT EXISTS login_logs(id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER,staff_id INTEGER,event TEXT,ip_address TEXT,user_agent TEXT,detail TEXT,created_at TEXT,FOREIGN KEY(user_id) REFERENCES users(id),FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS mistake_ledger(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER NOT NULL,entry_date TEXT NOT NULL,entry_type TEXT NOT NULL,amount INTEGER NOT NULL DEFAULT 0,title TEXT,notes TEXT,staff_note TEXT,created_by INTEGER,created_at TEXT,updated_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY,value TEXT NOT NULL);
    CREATE TABLE IF NOT EXISTS rules_acceptances(id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER NOT NULL,staff_id INTEGER,decision TEXT NOT NULL,accepted_at TEXT,ip_address TEXT,user_agent TEXT,FOREIGN KEY(user_id) REFERENCES users(id),FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS policy_acceptances(id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER NOT NULL,policy_version TEXT NOT NULL,decision TEXT NOT NULL,decided_at TEXT NOT NULL,ip_address TEXT,user_agent TEXT,UNIQUE(user_id,policy_version),FOREIGN KEY(user_id) REFERENCES users(id));
    CREATE TABLE IF NOT EXISTS rule_acceptances(id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER NOT NULL,decision TEXT NOT NULL,rules_version TEXT NOT NULL,created_at TEXT NOT NULL,ip_address TEXT,user_agent TEXT,FOREIGN KEY(user_id) REFERENCES users(id));
    ''')
    # Idempotent migrations for databases created by older releases.
    # CREATE TABLE IF NOT EXISTS does not add new columns to an existing table,
    # therefore every column used by the current application is checked here.
    migrations = {
      'offices': [('location','TEXT'),('status',"TEXT DEFAULT 'Aktif'")],
      'staff': [('gender',"TEXT DEFAULT 'Pria'"),('telegram_id','TEXT'),('telegram_username','TEXT'),('email','TEXT'),('agent_code','TEXT'),('cs_name','TEXT'),('office_id','INTEGER'),('position',"TEXT DEFAULT 'CS'"),('status',"TEXT DEFAULT 'Aktif'"),('join_date','TEXT'),('exit_date','TEXT'),('exit_reason','TEXT'),('notes','TEXT')],
      'users': [('role',"TEXT DEFAULT 'staff'"),('staff_id','INTEGER'),('office_id','INTEGER'),('is_active','INTEGER DEFAULT 1'),('must_change_password','INTEGER DEFAULT 1'),('allowed_menus',"TEXT DEFAULT '[\"my_dashboard\",\"inout\",\"mistakes\",\"history\",\"account\"]'"),('device_token','TEXT'),('last_login','TEXT'),('twofa_secret','TEXT'),('twofa_enabled','INTEGER DEFAULT 0')],
      'shifts': [('office_id','INTEGER'),('name','TEXT'),('code','TEXT'),('start_time','TEXT'),('end_time','TEXT'),('status',"TEXT DEFAULT 'Aktif'")],
      'shift_schedules': [('work_date','TEXT'),('staff_id','INTEGER'),('shift_id','INTEGER'),('office_id','INTEGER')],
      'channels': [('office_id','INTEGER'),('name','TEXT'),('category','TEXT'),('aliases',"TEXT DEFAULT ''"),('status',"TEXT DEFAULT 'Aktif'")],
      'assignments': [('assignment_batch_id','TEXT'),('work_date','TEXT'),('office_id','INTEGER'),('shift_id','INTEGER'),('staff_id','INTEGER'),('channel_id','INTEGER'),('category','TEXT'),('target','TEXT'),('start_time','TEXT'),('end_time','TEXT'),('is_active','INTEGER DEFAULT 1')],
      'offdays': [('staff_id','INTEGER'),('off_date','TEXT'),('notes','TEXT'),('created_at','TEXT')],
      'leaves': [('staff_id','INTEGER'),('reason','TEXT'),('out_at','TEXT'),('expected_at','TEXT'),('in_at','TEXT'),('status',"TEXT DEFAULT 'OUT'"),('late_minutes','INTEGER DEFAULT 0'),('fine','INTEGER DEFAULT 0'),('source','TEXT'),('notified_overdue','INTEGER DEFAULT 0'),('assignment_snapshot','TEXT'),('auto_in','INTEGER DEFAULT 0'),('device_token','TEXT')],
      'warnings': [('staff_id','INTEGER'),('type','TEXT'),('warning_date','TEXT'),('reason','TEXT'),('fine','INTEGER DEFAULT 0'),('notes','TEXT'),('created_by','INTEGER'),('created_at','TEXT')],
      'memos': [('staff_id','INTEGER'),('title','TEXT'),('category','TEXT'),('body','TEXT'),('priority',"TEXT DEFAULT 'Normal'"),('status',"TEXT DEFAULT 'Baru'"),('leader_reply','TEXT'),('created_at','TEXT'),('updated_at','TEXT')],
      'devices': [('device_name','TEXT'),('office_id','INTEGER'),('last_seen','INTEGER'),('page_url','TEXT'),('form_count','INTEGER DEFAULT 0'),('late_count','INTEGER DEFAULT 0')],
      'deposit_forms': [('device_id','TEXT'),('office_id','INTEGER'),('username','TEXT'),('game_id','TEXT'),('destination','TEXT'),('destination_account','TEXT'),('destination_owner','TEXT'),('form_time','TEXT'),('amount','TEXT'),('bank','TEXT'),('first_seen','INTEGER'),('last_seen','INTEGER'),('status',"TEXT DEFAULT 'pending'"),('alert_sent','INTEGER DEFAULT 0'),('staff_id','INTEGER'),('assignment_id','INTEGER'),('staff_status','TEXT'),('processed_at','TEXT'),('staff_name_snapshot','TEXT'),('cs_name_snapshot','TEXT'),('jobdesk_snapshot','TEXT'),('office_snapshot','TEXT'),('age_at_alert','INTEGER DEFAULT 0'),('alerted_at','TEXT'),('mapping_status','TEXT'),('balance_group','TEXT')],
      'audit_logs': [('user_id','INTEGER'),('action','TEXT'),('detail','TEXT'),('created_at','TEXT')],
    }
    for table, columns in migrations.items():
      for name, decl in columns:
        addcol(c, table, name, decl)
    # Fill safe defaults for rows originating from legacy schemas.
    c.execute("UPDATE shifts SET code=COALESCE(NULLIF(code,''), 'SHIFT-' || id), status=COALESCE(NULLIF(status,''),'Aktif')")
    migrate_global_shifts(c)
    c.execute("UPDATE offices SET status=COALESCE(NULLIF(status,''),'Aktif')")
    c.execute("DELETE FROM deposit_forms WHERE form_id IS NOT NULL AND form_id<>'' AND id NOT IN (SELECT MIN(id) FROM deposit_forms WHERE form_id IS NOT NULL AND form_id<>'' GROUP BY form_id)")
    c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_deposit_forms_form_id ON deposit_forms(form_id) WHERE form_id IS NOT NULL AND form_id<>''")
    c.execute('CREATE INDEX IF NOT EXISTS idx_deposit_forms_alert ON deposit_forms(alert_sent,first_seen)')
    c.execute('CREATE INDEX IF NOT EXISTS idx_deposit_forms_staff ON deposit_forms(staff_id,first_seen)')
    c.execute('CREATE INDEX IF NOT EXISTS idx_assignments_current ON assignments(work_date,office_id,is_active,staff_id,channel_id)')
    if not c.execute("SELECT 1 FROM offices WHERE name='Kantor Utama' LIMIT 1").fetchone(): c.execute("INSERT INTO offices(name,location,status) VALUES('Kantor Utama','-','Aktif')")
    oid=c.execute('SELECT id FROM offices ORDER BY id LIMIT 1').fetchone()[0]
    # Jangan bergantung pada UNIQUE constraint database lama; cek manual supaya startup tidak membuat shift duplikat.
    if not c.execute("SELECT 1 FROM shifts WHERE office_id IS NULL AND lower(name)=lower(?) LIMIT 1",('Pagi',)).fetchone(): c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(NULL,?,?,?,?,?)',('Pagi','P1','06:00','18:00','Aktif'))
    if not c.execute("SELECT 1 FROM shifts WHERE office_id IS NULL AND lower(name)=lower(?) LIMIT 1",('Malam',)).fetchone(): c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(NULL,?,?,?,?,?)',('Malam','M1','18:00','06:00','Aktif'))
    for k,v in {'late_minutes':str(LATE_MINUTES),'scan_seconds':str(SCAN_SECONDS)}.items(): c.execute('INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)',(k,v))
    if not c.execute('SELECT 1 FROM users WHERE username=?',(ADMIN_USERNAME,)).fetchone():
      c.execute('INSERT INTO users(username,password_hash,role,office_id,is_active,must_change_password,allowed_menus) VALUES(?,?,?,?,1,0,?)',(ADMIN_USERNAME,generate_password_hash(ADMIN_PASSWORD),'superadmin',oid,json.dumps(['*'])))
    # Migrasi sekali dari penugasan versi harian lama ke penugasan aktif CURRENT.
    for st in c.execute("SELECT id FROM staff WHERE status='Aktif'").fetchall():
      sid=st['id']
      if c.execute("SELECT 1 FROM shift_schedules WHERE work_date='CURRENT' AND staff_id=?",(sid,)).fetchone(): continue
      legacy=c.execute("SELECT * FROM shift_schedules WHERE staff_id=? AND work_date!='CURRENT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
      if not legacy: continue
      c.execute("INSERT OR IGNORE INTO shift_schedules(work_date,staff_id,shift_id,office_id) VALUES('CURRENT',?,?,?)",(sid,legacy['shift_id'],legacy['office_id']))
      jobs=c.execute("SELECT * FROM assignments WHERE staff_id=? AND work_date=? AND is_active=1 ORDER BY id",(sid,legacy['work_date'])).fetchall()
      if jobs:
       batch=uuid.uuid4().hex
       for a in jobs:
        c.execute("INSERT INTO assignments(assignment_batch_id,work_date,office_id,shift_id,staff_id,channel_id,category,target,start_time,end_time,is_active) VALUES(?,?,?,?,?,?,?,?,?,?,1)",(batch,'CURRENT',a['office_id'],a['shift_id'],sid,a['channel_id'],a['category'],a['target'],a['start_time'],a['end_time']))
    c.commit()

def audit(c,action,detail=''):
 uid=g.user['id'] if getattr(g,'user',None) else None
 c.execute('INSERT INTO audit_logs(user_id,action,detail,created_at) VALUES(?,?,?,?)',(uid,action,detail,now().isoformat()))
 if uid and not action.startswith('policy.'):
  c.execute('INSERT INTO login_logs(user_id,staff_id,event,ip_address,user_agent,detail,created_at) VALUES(?,?,?,?,?,?,?)',(uid,g.user['staff_id'], 'EDIT', request.headers.get('X-Forwarded-For',request.remote_addr), request.headers.get('User-Agent','')[:500], action+' · '+str(detail)[:500], now().isoformat()))
def tg_send(chat_id,text):
  if not BOT_TOKEN or not chat_id:return False
  try:return requests.post(f'https://api.telegram.org/bot{BOT_TOKEN}/sendMessage',json={'chat_id':chat_id,'text':text,'parse_mode':'HTML'},timeout=15).ok
  except Exception:return False

def tg_send_inout(text):
  targets=[]
  if INOUT_CHAT_ID: targets.append(str(INOUT_CHAT_ID))
  targets.extend(str(x) for x in INOUT_ADMIN_IDS)
  sent=False
  for chat_id in dict.fromkeys(targets):
   sent = tg_send(chat_id,text) or sent
  return sent

def tg_send_inout_admins(text):
  """Khusus notifikasi sensitif (AUTO IN): hanya ke ADMIN_IDS, bukan grup IN/OUT."""
  sent=False
  for chat_id in dict.fromkeys(str(x) for x in INOUT_ADMIN_IDS if str(x).strip()):
   sent = tg_send(chat_id,text) or sent
  return sent

def process_auto_in_overdue(c, current=None):
    """Close OUT sessions that are >=10 full minutes past expected_at.

    This is deliberately callable from both the background worker and request paths
    so AUTO IN does not depend on a single daemon thread staying healthy.
    Returns Telegram notification texts for rows actually closed by this call.
    """
    current=current or now()
    events=[]
    rows=c.execute("SELECT l.*,s.name,s.cs_name FROM leaves l JOIN staff s ON s.id=l.staff_id WHERE l.status='OUT'").fetchall()
    for l in rows:
        try:
            exp=datetime.fromisoformat(str(l['expected_at']))
            if exp.tzinfo is None:
                exp=exp.replace(tzinfo=WIB)
            else:
                exp=exp.astimezone(WIB)
            overdue_sec=(current-exp).total_seconds()
            if overdue_sec < 600:
                continue
            duration_sec=leave_duration_seconds(l,current)
            late=max(10,int(overdue_sec//60))
            cur=c.execute("UPDATE leaves SET in_at=?,status='AUTO_IN',late_minutes=?,fine=500000,auto_in=1 WHERE id=? AND status='OUT'",(current.isoformat(),late,l['id']))
            if cur.rowcount:
                dm,ds=divmod(duration_sec,60); dh,dm=divmod(dm,60)
                duration_text=(f"{dh} jam {dm} menit {ds} detik" if dh else f"{dm} menit {ds} detik")
                events.append(f"⚠️ <b>AUTO IN</b>\n👤 {l['name']} — {l['cs_name'] or '-'}\n📝 {str(l['reason']).title()}\n⏱ Durasi keluar: {duration_text}\n💸 Denda otomatis: Rp500.000\n✅ Slot OUT telah dibebaskan.")
        except Exception as row_error:
            print('[auto-in-row]', l['id'], row_error, flush=True)
    return events

def flush_auto_in_notifications(events):
    for text in events:
        try:
            tg_send_inout_admins(text)
        except Exception as notify_error:
            print('[auto-in-notify]', notify_error, flush=True)

@app.before_request
def before():
 g.user=None; g.policy_pending=False; g.theme=session.get('theme','dark')
 # Auto logout setelah 5 jam tanpa aktivitas untuk semua akun (Master/Leader/SPV/Staf).
 # Timestamp disimpan di session browser, jadi aktivitas di device lain tidak memperpanjang sesi ini.
 if session.get('uid'):
  try:
   last_activity=float(session.get('last_activity_ts') or 0)
  except Exception:
   last_activity=0
  current_ts=time.time()
  if last_activity and current_ts-last_activity >= 5*60*60:
   expired_uid=session.get('uid')
   try:
    with db_conn() as lc:
     u0=lc.execute('SELECT id,staff_id FROM users WHERE id=?',(expired_uid,)).fetchone()
     if u0:
      lc.execute('INSERT INTO login_logs(user_id,staff_id,event,ip_address,user_agent,detail,created_at) VALUES(?,?,?,?,?,?,?)',(u0['id'],u0['staff_id'],'AUTO_LOGOUT',request.headers.get('X-Forwarded-For',request.remote_addr),request.headers.get('User-Agent','')[:500],'Tidak ada aktivitas selama 5 jam',now().isoformat()))
      lc.commit()
   except Exception as idle_log_error:
    print('[idle-logout-log]',idle_log_error,flush=True)
   session.clear()
   flash('Sesi berakhir karena tidak ada aktivitas selama 5 jam. Silakan login kembali.','danger')
   return redirect(url_for('login'))
  # Polling realtime /api/* dan asset static tidak dihitung sebagai aktivitas user.
  if not request.path.startswith('/api/') and request.endpoint!='static':
   session['last_activity_ts']=current_ts
  with db_conn() as c:
   g.user=c.execute('SELECT * FROM users WHERE id=? AND is_active=1',(session['uid'],)).fetchone()
   g.allowed_menus=[]
   if g.user:
    try:g.allowed_menus=json.loads(g.user['allowed_menus'] or '[]')
    except Exception:g.allowed_menus=[]
   if g.user and g.user['role'] in ('staff','supervisor'):
    g.policy_pending=bool(session.get('policy_pending'))
   # Anti double-device saat staf sedang OUT. Session lama pada device lain ikut ditolak.
   if g.user and g.user['role']=='staff' and g.user['staff_id'] and request.endpoint not in ('login','logout','static'):
    active_leave=c.execute("SELECT device_token FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(g.user['staff_id'],)).fetchone()
    if active_leave:
     expected=(active_leave['device_token'] or g.user['device_token'] or '').strip()
     # Device yang membuat OUT tetap boleh terus memakai dashboard untuk menekan IN.
     # Token session diprioritaskan supaya POST IZIN OUT tidak membuat browser yang sama dianggap device baru.
     current=(session.get('browser_device_token') or request.cookies.get('om_device_id') or '').strip()
     if not expected or current!=expected:
      session.clear(); flash('Tidak bisa beda device login','danger'); return redirect(url_for('login'))

def login_required(fn):
 @wraps(fn)
 def w(*a,**k): return redirect(url_for('login')) if not g.user else fn(*a,**k)
 return w

def roles(*allowed):
 def deco(fn):
  @wraps(fn)
  def w(*a,**k):
   if not g.user:return redirect(url_for('login'))
   if g.user['role'] not in allowed:return ('Akses ditolak',403)
   return fn(*a,**k)
  return w
 return deco

def menu_allowed(menu):
 if not g.user:return False
 if g.user['role']!='staff':return True
 return '*' in getattr(g,'allowed_menus',[]) or menu in getattr(g,'allowed_menus',[])

def active_shift(c,office_id,when=None):
 when=when or now(); hm=when.strftime('%H:%M')
 for s in c.execute("SELECT * FROM shifts WHERE office_id IS NULL AND status='Aktif' ORDER BY start_time,name"):
  st=s['start_time']; en=s['end_time']; ok=(st<=hm<en) if st<en else (hm>=st or hm<en)
  if ok:return s
 return None


def staff_active_assignments(c,staff_id,when=None):
 when=when or now(); hm=when.strftime('%H:%M')
 rows=c.execute("""SELECT a.*,ch.name channel_name FROM assignments a LEFT JOIN channels ch ON ch.id=a.channel_id WHERE a.staff_id=? AND a.work_date='CURRENT' AND a.is_active=1 ORDER BY ch.category,ch.name""",(staff_id,)).fetchall()
 active=[]
 for r in rows:
  st=r['start_time'] or '00:00'; en=r['end_time'] or '23:59'; ok=(st<=hm<en) if st<en else (hm>=st or hm<en)
  if ok: active.append(r)
 return active

def find_assignment(c,office_id,target,when=None):
 when=when or now(); hm=when.strftime('%H:%M'); target_norm=re.sub(r'[^a-z0-9]','',target.lower())
 rows=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,s.telegram_id,s.agent_code,o.name office_name,o.location,sh.name shift_name,ch.name channel_name,ch.aliases
 FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id
 WHERE a.office_id=? AND a.work_date='CURRENT' AND a.is_active=1 AND s.status='Aktif' ''',(office_id,)).fetchall()
 for r in rows:
  st=r['start_time'] or '00:00'; en=r['end_time'] or '23:59'; ok=(st<=hm<en) if st<en else (hm>=st or hm<en)
  names=[r['channel_name'] or '',r['target'] or '']+[x.strip() for x in (r['aliases'] or '').split(',')]
  if ok and any(re.sub(r'[^a-z0-9]','',x.lower()) in target_norm or target_norm in re.sub(r'[^a-z0-9]','',x.lower()) for x in names if x): return r
 return None


def _norm_key(value):
 return re.sub(r'[^a-z0-9]+','',str(value or '').lower())

def _bank_tokens(value):
 text=str(value or '').upper()
 return {x for x in ('DANA','BCA','BRI','BNI','QRIS','MANDIRI','SEABANK','OVO','GOPAY','CIMB') if x in text}

def _source_bank_name(value):
 """Normalisasi BANK ASAL untuk membentuk jobdesk Gx-BANK."""
 text=re.sub(r'[^A-Z0-9]+',' ',str(value or '').upper()).strip()
 # Urutan lebih spesifik dulu.
 aliases=[
  ('DANA',('DANA',' DAN ')),('BCA',('BCA',)),('BRI',('BRI',)),('BNI',('BNI',)),
  ('MANDIRI',('MANDIRI',)),('SEABANK',('SEABANK','SEA BANK')),('QRIS',('QRIS',)),
  ('OVO',('OVO',)),('GOPAY',('GOPAY','GO PAY')),('CIMB',('CIMB',))]
 padded=' '+text+' '
 for canon,vals in aliases:
  if any(v in padded for v in vals): return canon
 return text.split()[0] if text else ''

def find_deposit_assignment_global(c,data,when=None):
 """Mapping GLOBAL: G1/G2 dari Balance + BANK ASAL => jobdesk G1-DANA dst.

 Extension tidak membawa kantor. Kantor dan nama CS selalu diturunkan dari Penugasan Kerja aktif.
 Bila jobdesk yang sama aktif di lebih dari satu staf pada saat yang sama, jangan menebak.
 """
 when=when or now(); hm=when.strftime('%H:%M')
 raw_group=' '.join(str(data.get(k) or '') for k in ('balanceGroup','group','bankOrigin','rowText','info'))
 gm=re.search(r'\bG\s*([0-9]+)\b',raw_group,re.I)
 group=f"G{gm.group(1)}" if gm else ''
 source_bank=_source_bank_name(data.get('sourceBank') or data.get('bank') or data.get('bankOrigin') or '')
 expected=f"{group}-{source_bank}" if group and source_bank else ''
 expected_norm=_norm_key(expected)
 rows=c.execute("""SELECT a.*,s.name staff_name,s.cs_name,s.telegram_id,s.agent_code,
 o.name office_name,o.location,sh.name shift_name,ch.name channel_name,ch.aliases,ch.category
 FROM assignments a JOIN staff s ON s.id=a.staff_id
 LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id
 LEFT JOIN channels ch ON ch.id=a.channel_id
 WHERE a.work_date='CURRENT' AND a.is_active=1 AND s.status='Aktif'""").fetchall()

 # Jika G belum berhasil dibaca dari DOM, jangan langsung kirim DANA/BCA tanpa CS.
 # Fallback aman: hanya gunakan assignment bila tepat SATU jobdesk aktif memakai bank asal tersebut.
 # Jika ada G1-DANA dan G2-DANA sekaligus, status tetap ambigu dan sistem tidak menebak.
 if not group and source_bank:
  bank_matches=[]
  for r in rows:
   st=r['start_time'] or '00:00'; en=r['end_time'] or '23:59'
   active=(st<=hm<en) if st<en else (hm>=st or hm<en)
   if not active: continue
   label=' '.join([r['channel_name'] or '',r['target'] or '',r['aliases'] or ''])
   lg=re.search(r'\bG\s*([0-9]+)\b',label,re.I)
   if lg and source_bank in _bank_tokens(label): bank_matches.append(r)
  if len(bank_matches)==1:
   r=bank_matches[0]
   label=' '.join([r['channel_name'] or '',r['target'] or '',r['aliases'] or ''])
   lg=re.search(r'\bG\s*([0-9]+)\b',label,re.I)
   inferred=f"G{lg.group(1)}-{source_bank}" if lg else (r['channel_name'] or r['target'] or source_bank)
   return r,'MATCHED_BANK_UNIQUE',inferred
  if len(bank_matches)>1:
   return None,'AMBIGUOUS_BANK',source_bank
  return None,'NO_GROUP_OR_BANK',source_bank

 if not expected_norm:
  return None,'NO_GROUP_OR_BANK',expected
 matches=[]
 for r in rows:
  st=r['start_time'] or '00:00'; en=r['end_time'] or '23:59'
  active=(st<=hm<en) if st<en else (hm>=st or hm<en)
  if not active: continue
  names=[r['channel_name'] or '',r['target'] or '']+[x.strip() for x in (r['aliases'] or '').split(',') if x.strip()]
  if any(_norm_key(x)==expected_norm for x in names if x): matches.append(r)
 if len(matches)==1: return matches[0],'MATCHED',expected
 if len(matches)>1: return None,'AMBIGUOUS',expected
 # Fallback ketat: group dan bank wajib sama, walau penulisan jobdesk punya teks tambahan.
 loose=[]
 for r in rows:
  st=r['start_time'] or '00:00'; en=r['end_time'] or '23:59'
  active=(st<=hm<en) if st<en else (hm>=st or hm<en)
  if not active: continue
  label=' '.join([r['channel_name'] or '',r['target'] or '',r['aliases'] or ''])
  lg=re.search(r'\bG\s*([0-9]+)\b',label,re.I)
  if lg and f"G{lg.group(1)}"==group and source_bank in _bank_tokens(label): loose.append(r)
 if len(loose)==1: return loose[0],'MATCHED',expected
 if len(loose)>1: return None,'AMBIGUOUS',expected
 return None,'NO_MATCH',expected

@app.route('/login',methods=['GET','POST'])
def login():
 if request.method=='POST':
  with db_conn() as c:
   u=c.execute('SELECT * FROM users WHERE username=? AND is_active=1',(request.form['username'].strip(),)).fetchone()
   if not u or not check_password_hash(u['password_hash'],request.form['password']): flash('ID atau password salah.','danger'); return render_template('login.html')
   if u['role']=='staff' and any(x in request.headers.get('User-Agent','').lower() for x in ['android','iphone','ipad','mobile']): flash('Akun staf hanya dapat login dari PC.','danger'); return render_template('login.html')
   device_cookie=(request.cookies.get('om_device_id') or '').strip()
   device_token=device_cookie or secrets.token_urlsafe(24)
   if u['role']=='staff' and u['staff_id']:
    active_leave=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(u['staff_id'],)).fetchone()
    if active_leave:
     expected_token=(active_leave['device_token'] or u['device_token'] or '').strip()
     # Saat sedang OUT, hanya browser/device yang membuat OUT tersebut yang boleh login ulang.
     if not device_cookie or not expected_token or device_cookie!=expected_token:
      flash('Tidak bisa beda device login','danger'); return render_template('login.html')
     device_token=expected_token
    else:
     c.execute('UPDATE users SET device_token=? WHERE id=?',(device_token,u['id']))
     c.commit()
   if u['twofa_enabled']:
    session['pending_uid']=u['id']; session['pending_device_token']=device_token
    resp=redirect(url_for('twofa_verify')); resp.set_cookie('om_device_id',device_token,max_age=31536000,httponly=True,samesite='Lax',secure=request.is_secure); return resp
   if u['role']=='superadmin':
    session['uid']=u['id']; session['policy_pending']=True; session['browser_device_token']=device_token; session['last_activity_ts']=time.time()
    c.execute('UPDATE users SET last_login=? WHERE id=?',(now().isoformat(),u['id'])); c.commit(); flash('Master wajib mengaktifkan 2FA sebelum melanjutkan.','danger')
    resp=redirect(url_for('twofa_setup')); resp.set_cookie('om_device_id',device_token,max_age=31536000,httponly=True,samesite='Lax',secure=request.is_secure); return resp
   session['uid']=u['id']; session['policy_pending']=True; session['browser_device_token']=device_token; session['last_activity_ts']=time.time()
   c.execute('UPDATE users SET last_login=? WHERE id=?',(now().isoformat(),u['id'])); c.execute('INSERT INTO login_logs(user_id,staff_id,event,ip_address,user_agent,detail,created_at) VALUES(?,?,?,?,?,?,?)',(u['id'],u['staff_id'],'LOGIN',request.headers.get('X-Forwarded-For',request.remote_addr),request.headers.get('User-Agent','')[:500],'Login berhasil',now().isoformat())); c.commit()
   resp=redirect(url_for('dashboard')); resp.set_cookie('om_device_id',device_token,max_age=31536000,httponly=True,samesite='Lax',secure=request.is_secure); return resp
 return render_template('login.html')
@app.route('/2fa/verify',methods=['GET','POST'])
def twofa_verify():
 uid=session.get('pending_uid')
 if not uid:return redirect(url_for('login'))
 with db_conn() as c:u=c.execute('SELECT * FROM users WHERE id=?',(uid,)).fetchone()
 if request.method=='POST':
  if totp_verify(u['twofa_secret'],request.form['code'].strip()):
   session.pop('pending_uid',None); session['uid']=uid; session['policy_pending']=True; session['last_activity_ts']=time.time()
   device_token=(session.pop('pending_device_token',None) or request.cookies.get('om_device_id') or '').strip(); session['browser_device_token']=device_token
   with db_conn() as c2: c2.execute('INSERT INTO login_logs(user_id,staff_id,event,ip_address,user_agent,detail,created_at) VALUES(?,?,?,?,?,?,?)',(u['id'],u['staff_id'],'LOGIN',request.headers.get('X-Forwarded-For',request.remote_addr),request.headers.get('User-Agent','')[:500],'Login 2FA berhasil',now().isoformat())); c2.commit()
   resp=redirect(url_for('dashboard'))
   if device_token: resp.set_cookie('om_device_id',device_token,max_age=31536000,httponly=True,samesite='Lax',secure=request.is_secure)
   return resp
  flash('Kode 2FA salah.','danger')
 return render_template('twofa.html')
@app.post('/policy/decision')
@login_required
def policy_decision():
 decision=(request.form.get('decision') or '').strip().lower()
 if decision not in ('setuju','tidak_setuju'): return ('Keputusan tidak valid',400)
 with db_conn() as c:
  existing=c.execute('SELECT id FROM policy_acceptances WHERE user_id=? AND policy_version=?',(g.user['id'],POLICY_VERSION)).fetchone()
  values=(decision,now().isoformat(),request.headers.get('X-Forwarded-For',request.remote_addr),request.headers.get('User-Agent','')[:500])
  if existing: c.execute('UPDATE policy_acceptances SET decision=?,decided_at=?,ip_address=?,user_agent=? WHERE id=?',values+(existing['id'],))
  else: c.execute('INSERT INTO policy_acceptances(user_id,policy_version,decision,decided_at,ip_address,user_agent) VALUES(?,?,?,?,?,?)',(g.user['id'],POLICY_VERSION)+values)
  audit(c,'policy.'+decision,POLICY_VERSION); c.commit()
 if decision=='tidak_setuju':
  session.clear(); return redirect(url_for('login',policy='declined'))
 session.pop('policy_pending',None)
 return redirect(request.form.get('next') or url_for('dashboard'))

@app.get('/logout')
def logout():
 uid=session.get('uid')
 if uid:
  try:
   with db_conn() as c:
    u=c.execute('SELECT * FROM users WHERE id=?',(uid,)).fetchone(); c.execute('INSERT INTO login_logs(user_id,staff_id,event,ip_address,user_agent,detail,created_at) VALUES(?,?,?,?,?,?,?)',(uid,u['staff_id'] if u else None,'LOGOUT',request.headers.get('X-Forwarded-For',request.remote_addr),request.headers.get('User-Agent','')[:500],'Logout',now().isoformat())); c.commit()
  except Exception: pass
 session.clear();return redirect(url_for('login'))

@app.get('/')
@login_required
def dashboard():
 if g.user['role']=='staff' and not menu_allowed('my_dashboard'): return ('Akses dashboard dinonaktifkan oleh Master.',403)
 with db_conn() as c:
  today=now().date().isoformat(); office_id=request.args.get('office_id',type=int) or g.user['office_id']
  offices=c.execute("SELECT * FROM offices WHERE status='Aktif'").fetchall(); params=[]; where=' WHERE 1=1 '
  if office_id:where+=' AND s.office_id=?';params.append(office_id)
  staff=c.execute('SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id'+where+' ORDER BY s.name',params).fetchall()
  assignments=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,o.name office_name,sh.name shift_name,ch.name channel_name,ch.category category FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id WHERE a.work_date='CURRENT' '''+(' AND a.office_id=?' if office_id else '')+' ORDER BY o.name,sh.start_time,ch.category,ch.name',(office_id,) if office_id else ()).fetchall()
  leaves=c.execute("SELECT l.*,s.name,s.cs_name,o.name office_name FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.status='OUT'"+(' AND s.office_id=?' if office_id else ''),(office_id,) if office_id else ()).fetchall()
  alerts=c.execute('''SELECT d.*,s.name staff_name,s.cs_name,o.name office_name FROM deposit_forms d LEFT JOIN staff s ON s.id=d.staff_id LEFT JOIN offices o ON o.id=d.office_id WHERE d.alert_sent=1'''+(' AND d.office_id=?' if office_id else '')+' ORDER BY d.id DESC LIMIT 50',(office_id,) if office_id else ()).fetchall()
  day_start=int(now().replace(hour=0,minute=0,second=0,microsecond=0).timestamp()); day_end=day_start+86400
  pending_rank=c.execute('''SELECT s.id,s.name,s.cs_name,o.name office_name,COUNT(f.id) pending_count,MAX(CAST((f.last_seen-f.first_seen)/60 AS INTEGER)) max_age FROM deposit_forms f JOIN staff s ON s.id=f.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE f.alert_sent=1 AND f.first_seen>=? AND f.first_seen<? '''+(' AND s.office_id=?' if office_id else '')+''' GROUP BY s.id ORDER BY pending_count DESC,max_age DESC LIMIT 10''',(day_start,day_end,office_id) if office_id else (day_start,day_end)).fetchall()
  stats={'staff':sum(1 for x in staff if x['status']=='Aktif'),'out':len(leaves),'alerts':sum(int(x['pending_count']) for x in pending_rank),'ex':sum(1 for x in staff if x['status']=='Ex Karyawan')}
 boards={}
 for r in assignments:
  key=f"{r['category'] or 'LAINNYA'}|{r['shift_name'] or '-'}"
  boards.setdefault(key,{'title':f"{(r['category'] or 'LAINNYA').upper()} {str(r['shift_name'] or '').upper()}",'items':[]})['items'].append(r)
 return render_template('dashboard.html',offices=offices,office_id=office_id,staff=staff,assignments=assignments,boards=list(boards.values()),leaves=leaves,pending_rank=pending_rank,stats=stats)

@app.route('/offices',methods=['GET','POST'])
@roles('superadmin','supervisor')
def offices_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; oid=f.get('id',type=int); vals=(f['name'].strip(),f.get('location','').strip(),f.get('status','Aktif'))
   if oid: c.execute('UPDATE offices SET name=?,location=?,status=? WHERE id=?',vals+(oid,)); audit(c,'office.update',f'id={oid}')
   else: c.execute('INSERT INTO offices(name,location,status) VALUES(?,?,?)',vals); audit(c,'office.create',vals[0])
   c.commit(); flash('Master kantor berhasil disimpan.','success'); return redirect(url_for('offices_page'))
  rows=c.execute('SELECT * FROM offices ORDER BY name').fetchall()
 return render_template('offices.html',rows=rows)

@app.post('/offices/<int:oid>/delete')
@roles('superadmin','supervisor')
def office_delete(oid):
 with db_conn() as c:
  office=c.execute('SELECT * FROM offices WHERE id=?',(oid,)).fetchone()
  if not office:
   flash('Kantor tidak ditemukan.','error'); return redirect(url_for('offices_page'))
  main=c.execute("SELECT * FROM offices WHERE name='Kantor Utama' ORDER BY id LIMIT 1").fetchone()
  if not main:
   c.execute("INSERT INTO offices(name,location,status) VALUES('Kantor Utama','-','Aktif')")
   main=c.execute("SELECT * FROM offices WHERE name='Kantor Utama' ORDER BY id LIMIT 1").fetchone()
  main_id=int(main['id'])
  if int(oid)==main_id:
   flash('Kantor Utama tidak dapat dihapus karena menjadi kantor fallback untuk data staf.','error'); return redirect(url_for('offices_page'))
  try:
   c.execute('BEGIN IMMEDIATE')
   moved_staff=c.execute('SELECT COUNT(*) n FROM staff WHERE office_id=?',(oid,)).fetchone()['n']
   # Staf dan akun yang masih berada di kantor yang dihapus otomatis dipindahkan ke Kantor Utama.
   c.execute('UPDATE staff SET office_id=? WHERE office_id=?',(main_id,oid))
   c.execute('UPDATE users SET office_id=? WHERE office_id=?',(main_id,oid))
   c.execute('UPDATE users SET office_id=? WHERE staff_id IN (SELECT id FROM staff WHERE office_id=?)',(main_id,main_id))
   # Penugasan/history tetap dipertahankan, tetapi referensi kantor diarahkan ke Kantor Utama agar FK tidak putus.
   c.execute('UPDATE assignments SET office_id=? WHERE office_id=?',(main_id,oid))
   c.execute('UPDATE shift_schedules SET office_id=? WHERE office_id=?',(main_id,oid))
   c.execute('UPDATE devices SET office_id=? WHERE office_id=?',(main_id,oid))
   c.execute('UPDATE deposit_forms SET office_id=? WHERE office_id=?',(main_id,oid))
   # Jobdesk bersifat global; lepaskan ikatan kantor lama.
   c.execute('UPDATE channels SET office_id=NULL WHERE office_id=?',(oid,))
   # Shift adalah GLOBAL. Jika masih ada sisa shift legacy per-kantor, gabungkan sekarang
   # agar penghapusan kantor tidak pernah membuat master shift baru per kantor.
   migrate_global_shifts(c)
   c.execute('DELETE FROM offices WHERE id=?',(oid,))
   audit(c,'office.delete',f"id={oid}; name={office['name']}; staff_moved={moved_staff}; fallback=Kantor Utama")
   c.commit()
   flash(f"Kantor {office['name']} berhasil dihapus. {moved_staff} staf dipindahkan otomatis ke Kantor Utama.",'success')
  except Exception:
   c.rollback(); raise
 return redirect(url_for('offices_page'))

@app.get('/offices/<int:oid>')
@roles('superadmin','supervisor','leader')
def office_detail(oid):
 with db_conn() as c:
  office=c.execute('SELECT * FROM offices WHERE id=?',(oid,)).fetchone()
  if not office:return ('Kantor tidak ditemukan',404)
  staff=c.execute('''SELECT s.*,u.username login_id,
    (SELECT COUNT(*) FROM warnings w WHERE w.staff_id=s.id) sp_count,
    (SELECT w.type FROM warnings w WHERE w.staff_id=s.id ORDER BY w.warning_date DESC,w.id DESC LIMIT 1) last_sp
    FROM staff s LEFT JOIN users u ON u.staff_id=s.id WHERE s.office_id=? ORDER BY CASE WHEN s.status='Aktif' THEN 0 ELSE 1 END,s.name''',(oid,)).fetchall()
  today=now().date().isoformat(); jobs=c.execute('''SELECT a.staff_id,ch.name,ch.category,sh.name shift_name,a.start_time,a.end_time FROM assignments a LEFT JOIN channels ch ON ch.id=a.channel_id LEFT JOIN shifts sh ON sh.id=a.shift_id WHERE a.office_id=? AND a.work_date='CURRENT' AND a.is_active=1 ORDER BY a.staff_id,ch.category,ch.name''',(oid,)).fetchall()
  jobmap={}
  for j in jobs:jobmap.setdefault(j['staff_id'],{'jobs':[],'shift':j['shift_name'],'hours':f"{j['start_time']}–{j['end_time']}"})['jobs'].append(j['name'] or '-')
  counts={'total':len(staff),'active':sum(1 for x in staff if x['status']=='Aktif'),'off':sum(1 for x in staff if x['status'] in ('Off','Off Day')),'ex':sum(1 for x in staff if x['status']=='Ex Karyawan')}
 return render_template('office_detail.html',office=office,staff=staff,jobmap=jobmap,counts=counts,today=today)

@app.route('/shifts',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def shifts_page():
 return redirect(url_for('operations_page'))

@app.post('/shifts/<int:sid>/delete')
@roles('superadmin','supervisor','leader')
def shift_delete(sid):
 with db_conn() as c:
  used=c.execute('SELECT 1 FROM assignments WHERE shift_id=? LIMIT 1',(sid,)).fetchone() or c.execute('SELECT 1 FROM shift_schedules WHERE shift_id=? LIMIT 1',(sid,)).fetchone()
  if used:
   c.execute("UPDATE shifts SET status='Nonaktif' WHERE id=?",(sid,)); flash('Shift pernah dipakai, jadi dinonaktifkan agar riwayat tetap aman.','success')
  else:
   c.execute('DELETE FROM shifts WHERE id=?',(sid,)); flash('Shift berhasil dihapus.','success')
  audit(c,'shift.delete_or_disable',str(sid)); c.commit()
 return redirect(url_for('shifts_page'))

@app.route('/channels',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def channels_page():
 # Jenis jobdesk bersifat GLOBAL. Kantor hanya menentukan penempatan staf pada Penugasan Kerja.
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; cid=f.get('id',type=int); vals=(None,f['name'].strip(),f['category'],f.get('aliases','').strip(),f.get('status','Aktif'))
   if not vals[1]: flash('Nama jobdesk wajib diisi.','danger'); return redirect(url_for('channels_page'))
   if cid:
    c.execute('UPDATE channels SET office_id=NULL,name=?,category=?,aliases=?,status=? WHERE id=?',(vals[1],vals[2],vals[3],vals[4],cid)); audit(c,'jobdesk.update',f'id={cid}')
   else:
    # Karena database lama dapat berisi jobdesk per kantor, cegah duplikat global berdasarkan nama+kategori.
    dup=c.execute('SELECT id FROM channels WHERE lower(name)=lower(?) AND lower(category)=lower(?) AND status!=? LIMIT 1',(vals[1],vals[2],'Dihapus')).fetchone()
    if dup: flash('Jobdesk dengan nama dan kategori tersebut sudah ada. Gunakan Edit.','danger'); return redirect(url_for('channels_page'))
    c.execute('INSERT INTO channels(office_id,name,category,aliases,status) VALUES(NULL,?,?,?,?)',(vals[1],vals[2],vals[3],vals[4])); audit(c,'jobdesk.create',vals[1])
   c.commit(); flash('Jenis jobdesk global berhasil disimpan.','success'); return redirect(url_for('channels_page'))
  rows=c.execute('SELECT ch.*,o.name office_name FROM channels ch LEFT JOIN offices o ON o.id=ch.office_id ORDER BY CASE ch.category WHEN "Deposit" THEN 1 WHEN "Withdraw" THEN 2 WHEN "Livechat" THEN 3 WHEN "Pulsa" THEN 4 WHEN "QRIS" THEN 5 ELSE 6 END,ch.name').fetchall()
 return render_template('channels.html',rows=rows)

@app.post('/channels/<int:cid>/delete')
@roles('superadmin','supervisor','leader')
def channel_delete(cid):
 with db_conn() as c:
  used=c.execute('SELECT 1 FROM assignments WHERE channel_id=? LIMIT 1',(cid,)).fetchone()
  if used: c.execute("UPDATE channels SET status='Nonaktif' WHERE id=?",(cid,)); flash('Channel sudah memiliki riwayat, jadi dinonaktifkan.','success')
  else: c.execute('DELETE FROM channels WHERE id=?',(cid,)); flash('Channel berhasil dihapus.','success')
  c.commit()
 return redirect(url_for('channels_page'))

@app.route('/staff',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def staff_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; sid=f.get('id',type=int); vals=(f['name'].strip(),f.get('gender','Pria'),f.get('telegram_id') or None,f.get('telegram_username','').strip(),f.get('email','').strip(),f.get('agent_code','').strip(),f.get('cs_name','').strip(),f.get('office_id',type=int),f.get('position','CS'),f.get('status','Aktif'),f.get('join_date') or None,f.get('notes','').strip())
   if sid:
    if not c.execute('SELECT 1 FROM staff WHERE id=?',(sid,)).fetchone(): flash('Data staf tidak ditemukan.','danger'); return redirect(url_for('staff_page'))
    c.execute('UPDATE staff SET name=?,gender=?,telegram_id=?,telegram_username=?,email=?,agent_code=?,cs_name=?,office_id=?,position=?,status=?,join_date=?,notes=? WHERE id=?',vals+(sid,))
   else:
    sid=c.execute('INSERT INTO staff(name,gender,telegram_id,telegram_username,email,agent_code,cs_name,office_id,position,status,join_date,notes) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)',vals).lastrowid
   if f.get('status','Aktif')=='Aktif':
    c.execute('UPDATE staff SET exit_date=NULL,exit_reason=NULL WHERE id=?',(sid,))
   elif f.get('status')=='Ex Karyawan':
    c.execute("UPDATE staff SET exit_date=COALESCE(exit_date,?),exit_reason=COALESCE(NULLIF(exit_reason,''),'Diubah dari Edit Data Staf') WHERE id=?",(now().date().isoformat(),sid))
   if f.get('login_id'):
    account_active=0 if f.get('status','Aktif')=='Ex Karyawan' else 1
    login_id=f['login_id'].strip(); existing_user=c.execute('SELECT id FROM users WHERE staff_id=?',(sid,)).fetchone(); username_owner=c.execute('SELECT id,staff_id FROM users WHERE username=?',(login_id,)).fetchone()
    if username_owner and (not existing_user or username_owner['id']!=existing_user['id']):
     c.rollback(); flash('ID login sudah dipakai akun lain.','danger'); return redirect(url_for('staff_page'))
    if existing_user:
     if f.get('password'): c.execute('UPDATE users SET username=?,password_hash=?,office_id=?,is_active=?,must_change_password=1 WHERE id=?',(login_id,generate_password_hash(f['password']),f.get('office_id',type=int),account_active,existing_user['id']))
     else: c.execute('UPDATE users SET username=?,office_id=?,is_active=? WHERE id=?',(login_id,f.get('office_id',type=int),account_active,existing_user['id']))
    else:
     pw=f.get('password') or secrets.token_urlsafe(6); c.execute('INSERT INTO users(username,password_hash,role,staff_id,office_id,is_active,must_change_password,allowed_menus) VALUES(?,?,?,?,?,?,1,?)',(login_id,generate_password_hash(pw),'staff',sid,f.get('office_id',type=int),account_active,json.dumps(['my_dashboard','inout','nawala','mistakes','history','account'])))
   audit(c,'staff.update' if f.get('id',type=int) else 'staff.create',f"Staf: {f['name'].strip()} · Agent: {f.get('agent_code','').strip() or '-'} · Kantor ID: {f.get('office_id',type=int) or '-'} · Jabatan: {f.get('position','CS')}"); c.commit(); flash('Data staf tersimpan.','success'); return redirect(url_for('staff_page'))
  report_date=request.args.get('date') or now().date().isoformat()
  rows=c.execute('''WITH current_assignment AS (
      SELECT staff_id, MIN(shift_id) AS shift_id FROM assignments
      WHERE work_date='CURRENT' AND is_active=1 GROUP BY staff_id
    )
    SELECT s.*,o.name office_name,u.username login_id,u.is_active account_active,
      COALESCE(ca.shift_id,ss.shift_id) shift_id,sh.name shift_name,sh.start_time shift_start,sh.end_time shift_end
    FROM staff s LEFT JOIN offices o ON o.id=s.office_id LEFT JOIN users u ON u.staff_id=s.id
    LEFT JOIN current_assignment ca ON ca.staff_id=s.id
    LEFT JOIN shift_schedules ss ON ss.staff_id=s.id AND ss.work_date='CURRENT'
    LEFT JOIN shifts sh ON sh.id=COALESCE(ca.shift_id,ss.shift_id)
    WHERE s.status NOT IN ('Ex Karyawan','Resign')
    ORDER BY CASE WHEN s.status="Aktif" THEN 0 ELSE 1 END,o.name,s.name''').fetchall()
  offices=c.execute('SELECT * FROM offices ORDER BY name').fetchall()
  filter_shifts=c.execute("SELECT id,name,start_time,end_time FROM shifts WHERE office_id IS NULL AND status='Aktif' ORDER BY start_time,name").fetchall()
  active_rows=[r for r in rows if r['status']=='Aktif']
  office_counts=[]
  for o in offices:
   members=[r for r in active_rows if r['office_id']==o['id']]
   all_members=[r for r in rows if r['office_id']==o['id']]
   office_counts.append({'id':o['id'],'name':o['name'],'location':o['location'],'count':len(members),'all_count':len(all_members)})
  # Jumlah staf per shift dihitung dari sumber shift yang sama dengan tabel /staff, agar angka dan filter selalu sinkron.
  shift_map={}
  for r in active_rows:
   if not r['shift_name']: continue
   key=(r['shift_name'],r['shift_start'] or '',r['shift_end'] or '')
   if key not in shift_map: shift_map[key]={'id':r['shift_id'],'shift_name':r['shift_name'],'name':r['shift_name'],'start_time':r['shift_start'],'end_time':r['shift_end'],'total':0}
   shift_map[key]['total']+=1
  shift_counts=sorted(shift_map.values(),key=lambda x:(x['start_time'] or '',x['shift_name']))
  ex_count=c.execute("SELECT COUNT(*) n FROM staff WHERE status IN ('Ex Karyawan','Resign')").fetchone()['n']; totals={'all':len(rows)+ex_count,'active':len(active_rows),'ex':ex_count,'scheduled':sum(int(x['total']) for x in shift_counts)}
 return render_template('staff.html',rows=rows,offices=offices,office_counts=office_counts,shift_counts=shift_counts,filter_shifts=filter_shifts,totals=totals,report_date=report_date)

@app.post('/staff/<int:sid>/delete')
@roles('superadmin','supervisor')
def staff_delete(sid):
 with db_conn() as c:
  st=c.execute('SELECT * FROM staff WHERE id=?',(sid,)).fetchone()
  if not st: flash('Staf tidak ditemukan.','danger'); return redirect(url_for('staff_page'))
  used=any(c.execute(q,(sid,)).fetchone() for q in [
   'SELECT 1 FROM assignments WHERE staff_id=? LIMIT 1','SELECT 1 FROM shift_schedules WHERE staff_id=? LIMIT 1','SELECT 1 FROM offdays WHERE staff_id=? LIMIT 1','SELECT 1 FROM leaves WHERE staff_id=? LIMIT 1','SELECT 1 FROM warnings WHERE staff_id=? LIMIT 1','SELECT 1 FROM deposit_forms WHERE staff_id=? LIMIT 1','SELECT 1 FROM memos WHERE staff_id=? LIMIT 1'])
  if used:
   c.execute("UPDATE staff SET status='Ex Karyawan',exit_date=COALESCE(exit_date,?) WHERE id=?",(now().date().isoformat(),sid)); c.execute('UPDATE users SET is_active=0 WHERE staff_id=?',(sid,)); flash('Staf memiliki riwayat. Data dipindahkan ke Ex Karyawan agar histori tetap aman.','success')
  else:
   c.execute('DELETE FROM users WHERE staff_id=?',(sid,)); c.execute('DELETE FROM staff WHERE id=?',(sid,)); flash('Data staf berhasil dihapus.','success')
  audit(c,'staff.delete_or_archive',f"Staf: {st['name']} · Status akhir: {c.execute('SELECT status FROM staff WHERE id=?',(sid,)).fetchone()['status'] if c.execute('SELECT 1 FROM staff WHERE id=?',(sid,)).fetchone() else 'Dihapus permanen'}"); c.commit()
 return redirect(url_for('staff_page'))

@app.get('/staff/<int:sid>/detail')
@roles('superadmin','supervisor','leader')
def staff_detail(sid):
 with db_conn() as c:
  st=c.execute('SELECT s.*,o.name office_name,o.location,u.username login_id,u.is_active account_active FROM staff s LEFT JOIN offices o ON o.id=s.office_id LEFT JOIN users u ON u.staff_id=s.id WHERE s.id=?',(sid,)).fetchone()
  if not st:return ('Staf tidak ditemukan',404)
  latest_shift=c.execute('''SELECT sh.name,sh.start_time,sh.end_time,ss.work_date FROM shift_schedules ss JOIN shifts sh ON sh.id=ss.shift_id WHERE ss.staff_id=? ORDER BY CASE WHEN ss.work_date='CURRENT' THEN 0 ELSE 1 END,ss.id DESC LIMIT 1''',(sid,)).fetchone()
  today=now().date().isoformat(); jobs=c.execute('''SELECT ch.name,ch.category,sh.name shift_name,a.start_time,a.end_time FROM assignments a LEFT JOIN channels ch ON ch.id=a.channel_id LEFT JOIN shifts sh ON sh.id=a.shift_id WHERE a.staff_id=? AND a.work_date='CURRENT' AND a.is_active=1 ORDER BY ch.category,ch.name''',(sid,)).fetchall()
  sp=c.execute('SELECT * FROM warnings WHERE staff_id=? ORDER BY warning_date DESC,id DESC',(sid,)).fetchall(); offices=c.execute("SELECT * FROM offices WHERE status='Aktif' ORDER BY name").fetchall(); cutoff=now()-timedelta(days=RETENTION_DAYS); pending_count=c.execute('SELECT COUNT(*) n FROM deposit_forms WHERE staff_id=? AND alert_sent=1 AND first_seen>=?',(sid,int(cutoff.timestamp()))).fetchone()['n']; leaves_count=c.execute('SELECT COUNT(*) n FROM leaves WHERE staff_id=? AND out_at>=?',(sid,cutoff.isoformat())).fetchone()['n']; mistake_rows=c.execute('SELECT entry_type,amount FROM mistake_ledger WHERE staff_id=?',(sid,)).fetchall(); mistake_total=sum(x['amount'] for x in mistake_rows if x['entry_type']=='MISTAKE'); mistake_cut=sum(x['amount'] for x in mistake_rows if x['entry_type']=='POTONGAN')
 return render_template('staff_detail.html',st=st,latest_shift=latest_shift,jobs=jobs,sp=sp,today=today,offices=offices,pending_count=pending_count,leaves_count=leaves_count,mistake_total=mistake_total,mistake_remaining=max(0,mistake_total-mistake_cut))

@app.post('/staff/<int:sid>/reset-password')
@roles('superadmin','supervisor','leader')
def reset_password(sid):
 pw=request.form.get('password') or secrets.token_urlsafe(7)
 with db_conn() as c:c.execute('UPDATE users SET password_hash=?,must_change_password=1 WHERE staff_id=?',(generate_password_hash(pw),sid));c.commit()
 flash('Password direset. Password baru: '+pw,'success');return redirect(url_for('staff_page'))

@app.route('/offdays',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def offdays_page():
 flash('Menu Off Day sudah dihapus. Pengaturan staf harian sekarang dipusatkan di Penugasan Kerja.','success')
 return redirect(url_for('operations_page'))

@app.post('/offdays/<int:oid>/delete')
@roles('superadmin','supervisor','leader')
def offday_delete(oid):
 return redirect(url_for('operations_page'))

@app.get('/audit')
@roles('superadmin','supervisor')
def audit_page():
 with db_conn() as c:
  rows=c.execute('''SELECT a.*,u.username FROM audit_logs a LEFT JOIN users u ON u.id=a.user_id ORDER BY a.id DESC LIMIT 500''').fetchall()
 return render_template('audit.html',rows=rows)

@app.route('/users',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def users_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; staff_id=f.get('staff_id',type=int); st=c.execute('SELECT * FROM staff WHERE id=?',(staff_id,)).fetchone()
   if not st:flash('Staf tidak ditemukan.','danger');return redirect(url_for('users_page'))
   role=f.get('role','staff')
   if g.user['role']=='leader' and role not in ('staff','leader'): role='staff'
   menus=f.getlist('menus'); username=f['username'].strip(); existing=c.execute('SELECT * FROM users WHERE staff_id=?',(staff_id,)).fetchone(); owner=c.execute('SELECT * FROM users WHERE username=?',(username,)).fetchone()
   if owner and (not existing or owner['id']!=existing['id']):flash('Username sudah dipakai akun lain.','danger');return redirect(url_for('users_page'))
   active=1 if f.get('is_active') else 0
   if existing:
    if f.get('password'):c.execute('UPDATE users SET username=?,password_hash=?,role=?,office_id=?,is_active=?,allowed_menus=?,must_change_password=1 WHERE id=?',(username,generate_password_hash(f['password']),role,st['office_id'],active,json.dumps(menus),existing['id']))
    else:c.execute('UPDATE users SET username=?,role=?,office_id=?,is_active=?,allowed_menus=? WHERE id=?',(username,role,st['office_id'],active,json.dumps(menus),existing['id']))
   else:
    pw=f.get('password') or secrets.token_urlsafe(7);c.execute('INSERT INTO users(username,password_hash,role,staff_id,office_id,is_active,must_change_password,allowed_menus) VALUES(?,?,?,?,?,?,1,?)',(username,generate_password_hash(pw),role,staff_id,st['office_id'],active,json.dumps(menus)))
   audit(c,'user.access.save',f'staff={staff_id} role={role} menus={menus}');c.commit();flash('Akses akun berhasil disimpan.','success');return redirect(url_for('users_page'))
  rows=c.execute('SELECT u.*,s.name staff_name,o.name office_name FROM users u LEFT JOIN staff s ON s.id=u.staff_id LEFT JOIN offices o ON o.id=u.office_id WHERE u.staff_id IS NOT NULL ORDER BY s.name').fetchall();staff=c.execute("SELECT * FROM staff WHERE status='Aktif' ORDER BY name").fetchall()
 return render_template('users.html',rows=rows,staff=staff)

@app.post('/users/reset-device/<int:uid>')
@roles('superadmin','supervisor','leader')
def user_reset_device(uid):
 with db_conn() as c:c.execute('UPDATE users SET device_token=NULL WHERE id=?',(uid,));audit(c,'user.device.reset',f'id={uid}');c.commit()
 flash('Ikatan PC berhasil direset.','success');return redirect(url_for('users_page'))

@app.route('/account',methods=['GET','POST'])
@login_required
def account_page():
 if request.method=='POST':
  with db_conn() as c:
   u=c.execute('SELECT * FROM users WHERE id=?',(g.user['id'],)).fetchone()
   if not check_password_hash(u['password_hash'],request.form['old_password']):flash('Password lama salah.','danger')
   elif len(request.form['new_password'])<8:flash('Password baru minimal 8 karakter.','danger')
   else:c.execute('UPDATE users SET password_hash=?,must_change_password=0 WHERE id=?',(generate_password_hash(request.form['new_password']),u['id']));c.commit();flash('Password berhasil diganti.','success')
 return render_template('account.html')

@app.route('/2fa/setup',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def twofa_setup():
 with db_conn() as c:
  u=c.execute('SELECT * FROM users WHERE id=?',(g.user['id'],)).fetchone(); secret=u['twofa_secret'] or base64.b32encode(secrets.token_bytes(20)).decode().rstrip('=')
  if request.method=='POST':
   if totp_verify(secret,request.form['code'].strip()):c.execute('UPDATE users SET twofa_secret=?,twofa_enabled=1 WHERE id=?',(secret,u['id']));c.commit();flash('2FA aktif.','success');return redirect(url_for('dashboard'))
   flash('Kode salah.','danger')
  uri=f"otpauth://totp/OMTOGEL%20Staff:{u['username']}?secret={secret}&issuer=OMTOGEL%20Staff"
 return render_template('twofa_setup.html',secret=secret,uri=uri)

@app.route('/operations',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def operations_page():
 """Penugasan Kerja GLOBAL.

 Tidak ada filter kantor untuk menambah/mengedit penugasan. Kantor selalu mengikuti
 profil staf. Shift dan Master Jobdesk juga global. Board menampilkan seluruh staf
 aktif yang mempunyai penugasan CURRENT dari semua kantor.
 """
 with db_conn() as c:
  work_date='CURRENT'
  if request.method=='POST':
   f=request.form; action=(f.get('action') or '').strip()
   try:
    if action=='shift_save':
     sid=f.get('shift_id',type=int)
     vals=((f.get('name') or '').strip(),(f.get('code') or '').strip(),f.get('start_time') or '',f.get('end_time') or '',f.get('status') or 'Aktif')
     if not vals[0] or not vals[2] or not vals[3]: raise ValueError('Nama shift, jam mulai, dan jam selesai wajib diisi.')
     dup=c.execute("SELECT id FROM shifts WHERE office_id IS NULL AND lower(name)=lower(?) AND id!=COALESCE(?,0) LIMIT 1",(vals[0],sid)).fetchone()
     if dup: raise ValueError('Nama shift global sudah digunakan. Gunakan Edit pada shift tersebut.')
     if sid:
      before=c.execute('SELECT * FROM shifts WHERE id=?',(sid,)).fetchone()
      if not before: raise ValueError('Shift tidak ditemukan.')
      c.execute('UPDATE shifts SET office_id=NULL,name=?,code=?,start_time=?,end_time=?,status=? WHERE id=?',vals+(sid,))
      audit(c,'operations.shift.update',f"Edit Shift Global: {before['name']} → {vals[0]} · Jam {before['start_time']}–{before['end_time']} → {vals[2]}–{vals[3]} · Status {before['status']} → {vals[4]}")
     else:
      c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(NULL,?,?,?,?,?)',vals)
      audit(c,'operations.shift.create',f"Tambah Shift Global: {vals[0]} · {vals[2]}–{vals[3]}")
     c.commit(); flash('Shift global berhasil disimpan.','success')

    elif action=='shift_delete':
     sid=f.get('shift_id',type=int)
     if not sid: raise ValueError('Shift tidak valid.')
     sh=c.execute('SELECT * FROM shifts WHERE id=?',(sid,)).fetchone()
     if not sh: raise ValueError('Shift tidak ditemukan.')
     used=c.execute('SELECT 1 FROM assignments WHERE shift_id=? LIMIT 1',(sid,)).fetchone() or c.execute('SELECT 1 FROM shift_schedules WHERE shift_id=? LIMIT 1',(sid,)).fetchone()
     if used:
      c.execute("UPDATE shifts SET status='Nonaktif' WHERE id=?",(sid,))
      audit(c,'operations.shift.disable',f"Nonaktifkan Shift Global: {sh['name']}")
      flash('Shift sudah pernah dipakai, jadi dinonaktifkan agar riwayat tetap aman.','success')
     else:
      c.execute('DELETE FROM shifts WHERE id=?',(sid,))
      audit(c,'operations.shift.delete',f"Hapus Shift Global: {sh['name']}")
      flash('Shift berhasil dihapus.','success')
     c.commit()

    elif action=='assignment_delete':
     staff_id=f.get('staff_id',type=int)
     if not staff_id: raise ValueError('Staf tidak valid.')
     st=c.execute('SELECT name,cs_name FROM staff WHERE id=?',(staff_id,)).fetchone()
     jobs=c.execute("""SELECT COALESCE(ch.name,a.target,'-') name FROM assignments a
                       LEFT JOIN channels ch ON ch.id=a.channel_id
                       WHERE a.work_date=? AND a.staff_id=? AND a.is_active=1 ORDER BY a.id""",(work_date,staff_id)).fetchall()
     c.execute('DELETE FROM assignments WHERE work_date=? AND staff_id=?',(work_date,staff_id))
     c.execute('DELETE FROM shift_schedules WHERE work_date=? AND staff_id=?',(work_date,staff_id))
     audit(c,'operations.assignment.delete',f"Hapus Penugasan: {st['name'] if st else staff_id} · Jobdesk: {', '.join(x['name'] for x in jobs) or '-'}")
     c.commit(); flash('Penugasan staf berhasil dihapus.','success')

    elif action=='assignment_save':
     staff_id=f.get('staff_id',type=int); shift_id=f.get('shift_id',type=int)
     channel_ids=[]
     for raw in f.getlist('channel_ids'):
      try:
       cid=int(raw)
       if cid not in channel_ids: channel_ids.append(cid)
      except (TypeError,ValueError): pass
     if not staff_id: raise ValueError('Pilih staf terlebih dahulu.')
     if not shift_id: raise ValueError('Pilih shift.')
     if not channel_ids: raise ValueError('Pilih minimal 1 jobdesk.')
     st=c.execute("SELECT * FROM staff WHERE id=? AND status='Aktif'",(staff_id,)).fetchone()
     sh=c.execute("SELECT * FROM shifts WHERE id=? AND office_id IS NULL AND status='Aktif'",(shift_id,)).fetchone()
     if not st: raise ValueError('Staf tidak ditemukan atau tidak aktif.')
     if not sh: raise ValueError('Shift global tidak valid atau tidak aktif.')
     office_id=st['office_id']
     if not office_id: raise ValueError('Kantor staf belum diatur di Data Staf.')
     valid=[]
     for cid in channel_ids:
      ch=c.execute("SELECT * FROM channels WHERE id=? AND status='Aktif'",(cid,)).fetchone()
      if ch: valid.append(ch)
     if len(valid)!=len(channel_ids): raise ValueError('Ada jobdesk yang sudah nonaktif atau tidak ditemukan.')


     old=c.execute('''SELECT sh.name shift_name,GROUP_CONCAT(COALESCE(ch.name,a.target), ', ') jobs
                      FROM assignments a LEFT JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id
                      WHERE a.work_date=? AND a.staff_id=? AND a.is_active=1 GROUP BY a.staff_id''',(work_date,staff_id)).fetchone()
     sched=c.execute('SELECT id FROM shift_schedules WHERE work_date=? AND staff_id=?',(work_date,staff_id)).fetchone()
     if sched: c.execute('UPDATE shift_schedules SET shift_id=?,office_id=? WHERE id=?',(shift_id,office_id,sched['id']))
     else: c.execute('INSERT INTO shift_schedules(work_date,staff_id,shift_id,office_id) VALUES(?,?,?,?)',(work_date,staff_id,shift_id,office_id))
     c.execute('DELETE FROM assignments WHERE work_date=? AND staff_id=?',(work_date,staff_id))
     batch_id=uuid.uuid4().hex
     start_time=f.get('start_time') or sh['start_time']; end_time=f.get('end_time') or sh['end_time']
     for ch in valid:
      c.execute('''INSERT INTO assignments(assignment_batch_id,work_date,office_id,shift_id,staff_id,channel_id,category,target,start_time,end_time,is_active)
                   VALUES(?,?,?,?,?,?,?,?,?,?,1)''',(batch_id,work_date,office_id,shift_id,staff_id,ch['id'],ch['category'],ch['name'],start_time,end_time))
     new_jobs=', '.join(x['name'] for x in valid)
     if old:
      audit(c,'operations.assignment.update',f"Edit Penugasan: {st['name']} · Shift {old['shift_name'] or '-'} → {sh['name']} · Jobdesk {old['jobs'] or '-'} → {new_jobs}")
     else:
      audit(c,'operations.assignment.create',f"Tambah Penugasan: {st['name']} · Shift {sh['name']} · Jobdesk {new_jobs}")
     c.commit(); flash('Penugasan staf berhasil disimpan.','success')

    else:
     raise ValueError('Aksi tidak dikenal.')
   except sqlite3.IntegrityError:
    c.rollback(); flash('Data bentrok dengan data yang sudah ada. Periksa kembali shift dan penugasan staf.','danger')
   except ValueError as e:
    c.rollback(); flash(str(e),'danger')
   return redirect(url_for('operations_page'))

  c.execute('''UPDATE assignments SET office_id=(SELECT s.office_id FROM staff s WHERE s.id=assignments.staff_id)
               WHERE work_date='CURRENT' AND staff_id IS NOT NULL
                 AND COALESCE(office_id,0) != COALESCE((SELECT s.office_id FROM staff s WHERE s.id=assignments.staff_id),0)''')
  c.execute('''UPDATE shift_schedules SET office_id=(SELECT s.office_id FROM staff s WHERE s.id=shift_schedules.staff_id)
               WHERE work_date='CURRENT' AND staff_id IS NOT NULL
                 AND COALESCE(office_id,0) != COALESCE((SELECT s.office_id FROM staff s WHERE s.id=shift_schedules.staff_id),0)''')
  c.commit()

  shifts=c.execute("SELECT * FROM shifts WHERE office_id IS NULL ORDER BY CASE WHEN status='Aktif' THEN 0 ELSE 1 END,start_time,name").fetchall()
  staff=c.execute("""SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id
                     WHERE s.status='Aktif' ORDER BY s.name""").fetchall()
  channels=c.execute("""SELECT * FROM channels WHERE status='Aktif'
                        ORDER BY CASE category WHEN 'Deposit' THEN 1 WHEN 'Withdraw' THEN 2 WHEN 'Livechat' THEN 3 WHEN 'Pulsa' THEN 4 WHEN 'QRIS' THEN 5 ELSE 6 END,name""").fetchall()
  raw=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,s.email,s.agent_code,s.office_id staff_office_id,
                          o.name office_name,sh.name shift_name,sh.code shift_code,sh.start_time shift_start,sh.end_time shift_end,
                          ch.name channel_name,ch.category channel_category
                   FROM assignments a JOIN staff s ON s.id=a.staff_id
                   LEFT JOIN offices o ON o.id=s.office_id
                   JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id
                   WHERE a.work_date=? AND a.is_active=1 AND s.status='Aktif'
                   ORDER BY sh.start_time,s.name,ch.category,ch.name''',(work_date,)).fetchall()
  groups={}
  for r in raw:
   gd=groups.setdefault(r['staff_id'],{
    'staff_id':r['staff_id'],'staff_name':r['staff_name'],'cs_name':r['cs_name'],'email':r['email'],'agent_code':r['agent_code'],
    'office_id':r['staff_office_id'],'office_name':r['office_name'],'shift_id':r['shift_id'],'shift_name':r['shift_name'],
    'shift_code':r['shift_code'],'start_time':r['start_time'],'end_time':r['end_time'],'channel_ids':[],'channels':[]})
   if r['channel_id'] not in gd['channel_ids']: gd['channel_ids'].append(r['channel_id'])
   gd['channels'].append({'id':r['channel_id'],'name':r['channel_name'] or r['target'] or 'Belum ada jobdesk','category':r['channel_category'] or r['category'] or 'Lainnya'})

  by_shift={}
  for sh in shifts:
   if sh['status']=='Aktif': by_shift[sh['id']]={'shift':sh,'staff':[]}
  for gd in groups.values():
   sh=c.execute('SELECT * FROM shifts WHERE id=?',(gd['shift_id'],)).fetchone()
   if sh: by_shift.setdefault(gd['shift_id'],{'shift':sh,'staff':[]})['staff'].append(gd)
  assigned_ids=set(groups.keys())
  unassigned=[x for x in staff if x['id'] not in assigned_ids]

  assigned_rows=list(groups.values())

  edit_staff=request.args.get('edit_staff',type=int)
  edit_row=groups.get(edit_staff)
  totals={'active_staff':len(staff),'assigned':len(groups),'unassigned':len(unassigned),'active_shifts':sum(1 for x in shifts if x['status']=='Aktif')}
 return render_template('operations.html',shifts=shifts,staff=staff,channels=channels,by_shift=list(by_shift.values()),assigned_rows=assigned_rows,unassigned=unassigned,edit_row=edit_row,totals=totals)

@app.route('/assignments',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def assignments_page():
 return redirect(url_for('operations_page'))

@app.route('/inout',methods=['GET','POST'])
@login_required
def inout_page():
 if g.user['role']=='staff' and not menu_allowed('inout'): return ('Akses IN/OUT dinonaktifkan oleh Master.',403)
 if not g.user['staff_id']: return ('Akun ini tidak terhubung ke Data Staf.',400)
 sid=g.user['staff_id']
 with db_conn() as c:
  auto_events=process_auto_in_overdue(c); c.commit(); flush_auto_in_notifications(auto_events)
  staff=c.execute('SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE s.id=?',(sid,)).fetchone()
  ass_rows=staff_active_assignments(c,sid,now()); ass=ass_rows[0] if ass_rows else None; jobdesk_text=', '.join((r['channel_name'] or r['target'] or '-') for r in ass_rows) or '-'
  active=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
  if request.method=='POST':
   action=request.form.get('action','')
   if action=='out':
    reason=request.form.get('reason','')
    if reason not in DURATIONS:
     flash('Jenis izin tidak valid.','danger'); return redirect(url_for('inout_page'))
    # Transaksi eksklusif pendek agar batas 5 orang tidak bisa terlewati walau beberapa staf klik bersamaan.
    with lock:
     try:
      c.execute('BEGIN IMMEDIATE')
      active_now=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
      active_count=c.execute("SELECT COUNT(*) n FROM leaves WHERE status='OUT'").fetchone()['n']
      if active_now:
       c.rollback(); flash('Kamu masih dalam status izin keluar. Tekan IN KEMBALI setelah kembali.','danger')
      elif active_count>=MAX_ACTIVE_LEAVES:
       c.rollback(); flash('Silakan dicoba beberapa saat lagi karena OUT sudah mencapai jumlah maksimal 5 orang, atau hubungi Leader.','danger')
      else:
       out=now(); exp=out+timedelta(minutes=DURATIONS[reason]); snap=json.dumps({'jobdesk':jobdesk_text,'cs':staff['cs_name'],'office':staff['office_name']})
       device_token=(request.cookies.get('om_device_id') or session.get('browser_device_token') or g.user['device_token'] or '').strip()
       if not device_token: device_token=secrets.token_urlsafe(24)
       session['browser_device_token']=device_token
       session['last_activity_ts']=time.time()
       c.execute('UPDATE users SET device_token=? WHERE id=?',(device_token,g.user['id']))
       c.execute('INSERT INTO leaves(staff_id,reason,out_at,expected_at,status,source,assignment_snapshot,device_token) VALUES(?,?,?,?,?,?,?,?)',(sid,reason,out.isoformat(),exp.isoformat(),'OUT','dashboard',snap,device_token)); c.commit()
       tg_send_inout(f"🚪 <b>IZIN KELUAR</b>\n👤 {staff['name']} — {staff['cs_name'] or '-'}\n💼 {jobdesk_text}\n📝 {reason.title()}\n⏳ Estimasi kembali: {exp.strftime('%H:%M')} WIB")
     except Exception:
      c.rollback(); raise
   elif action=='in':
    active_now=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
    if not active_now:
     flash('Tidak ada izin aktif untuk akun ini.','danger')
    else:
     current_device=(request.cookies.get('om_device_id') or session.get('browser_device_token') or '').strip()
     leave_device=(active_now['device_token'] or g.user['device_token'] or '').strip()
     if leave_device and current_device!=leave_device:
      flash('Tidak bisa beda device login','danger'); return redirect(url_for('inout_page'))
     t=now(); exp=datetime.fromisoformat(active_now['expected_at'])
     # Denda hanya dihitung setelah lewat satu menit penuh. Contoh: lewat 30 detik = Rp0, lewat 1:00 = Rp50.000.
     late=max(0,int((t-exp).total_seconds()//60)); fine=late*50000 if 1<=late<=9 else (500000 if late>=10 else 0)
     duration_sec=leave_duration_seconds(active_now,t)
     c.execute("UPDATE leaves SET in_at=?,status='IN',late_minutes=?,fine=?,auto_in=0 WHERE id=?",(t.isoformat(),late,fine,active_now['id'])); c.commit()
     dm,ds=divmod(duration_sec,60); dh,dm=divmod(dm,60); duration_text=(f"{dh} jam {dm} menit {ds} detik" if dh else f"{dm} menit {ds} detik")
     tg_send_inout(f"✅ <b>SUDAH KEMBALI</b>\n👤 {staff['name']}\n⏱ Durasi keluar: {duration_text}\n⏱ Terlambat: {late} menit\n💸 Denda: Rp{fine:,}")
   return redirect(url_for('inout_page'))
  active=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
  active_count=c.execute("SELECT COUNT(*) n FROM leaves WHERE status='OUT'").fetchone()['n']
  month_start=now().replace(day=1,hour=0,minute=0,second=0,microsecond=0); history_raw=c.execute('SELECT * FROM leaves WHERE staff_id=? AND out_at>=? ORDER BY id DESC LIMIT 100',(sid,month_start.isoformat())).fetchall()
  history=[]
  for r in history_raw:
   d=dict(r); d['duration_seconds']=leave_duration_seconds(r); history.append(d)
 return render_template('inout.html',staff=staff,active=active,history=history,assignment=ass,assignments=ass_rows,jobdesk_text=jobdesk_text,durations=DURATIONS,active_count=active_count,max_active=MAX_ACTIVE_LEAVES,retention_days=RETENTION_DAYS)

@app.get('/api/inout/active')
@login_required
def api_inout_active():
 with db_conn() as c:
  auto_events=process_auto_in_overdue(c); c.commit(); flush_auto_in_notifications(auto_events)
  rows=c.execute("""SELECT l.id,l.staff_id,l.reason,l.out_at,l.expected_at,s.name,s.cs_name,o.name office_name
                    FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id
                    WHERE l.status='OUT' ORDER BY l.out_at ASC""").fetchall()
 data=[]
 for r in rows:
  data.append({'id':r['id'],'staff_id':r['staff_id'],'name':r['name'],'cs_name':r['cs_name'] or '-', 'office_name':r['office_name'] or '-', 'reason':r['reason'], 'out_at':r['out_at'], 'expected_at':r['expected_at']})
 return jsonify({'ok':True,'count':len(data),'max':MAX_ACTIVE_LEAVES,'is_full':len(data)>=MAX_ACTIVE_LEAVES,'items':data,'server_time':now().isoformat()})


@app.get('/inout-live')
@roles('superadmin','supervisor','leader')
def inout_live_page():
 with db_conn() as c:
  auto_events=process_auto_in_overdue(c); c.commit(); flush_auto_in_notifications(auto_events)
  today_start=now().replace(hour=0,minute=0,second=0,microsecond=0).isoformat()
  recent=c.execute('''SELECT l.*,s.name,s.cs_name,o.name office_name FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.out_at>=? ORDER BY l.id DESC LIMIT 100''',(today_start,)).fetchall()
 return render_template('inout_live.html',recent=recent,max_active=MAX_ACTIVE_LEAVES)

@app.route('/warnings',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def warnings_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; wid=f.get('id',type=int); vals=(f.get('staff_id',type=int),f['type'],f['warning_date'],f['reason'].strip(),f.get('fine',type=int) or 0,f.get('notes','').strip())
   if wid:
    c.execute('UPDATE warnings SET staff_id=?,type=?,warning_date=?,reason=?,fine=?,notes=? WHERE id=?',vals+(wid,)); stn=c.execute('SELECT name FROM staff WHERE id=?',(vals[0],)).fetchone(); audit(c,'warning.update',f"Staf: {stn['name'] if stn else vals[0]} · {vals[1]} · {vals[2]} · {vals[3]}")
   else:
    c.execute('INSERT INTO warnings(staff_id,type,warning_date,reason,fine,notes,created_by,created_at) VALUES(?,?,?,?,?,?,?,?)',vals+(g.user['id'],now().isoformat())); stn=c.execute('SELECT name FROM staff WHERE id=?',(vals[0],)).fetchone(); audit(c,'warning.create',f"Staf: {stn['name'] if stn else vals[0]} · {vals[1]} · {vals[2]} · {vals[3]}")
   c.commit(); flash('Data SP berhasil disimpan.','success'); return redirect(url_for('warnings_page'))
  rows=c.execute('SELECT w.*,s.name,s.cs_name,o.name office_name FROM warnings w JOIN staff s ON s.id=w.staff_id LEFT JOIN offices o ON o.id=s.office_id ORDER BY w.warning_date DESC,w.id DESC').fetchall(); staff=c.execute("SELECT * FROM staff WHERE status!='Ex Karyawan' ORDER BY name").fetchall()
 return render_template('warnings.html',rows=rows,staff=staff)

@app.post('/warnings/<int:wid>/delete')
@roles('superadmin','supervisor')
def warning_delete(wid):
 with db_conn() as c:
  old=c.execute('SELECT * FROM warnings WHERE id=?',(wid,)).fetchone()
  if old: audit(c,'warning.delete',json.dumps(dict(old),default=str)); c.execute('DELETE FROM warnings WHERE id=?',(wid,)); c.commit(); flash('SP berhasil dihapus.','success')
 return redirect(url_for('warnings_page'))

@app.route('/former',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def former_page():
 with db_conn() as c:
  if request.method=='POST':
   sid=request.form.get('staff_id',type=int); exit_date=request.form.get('exit_date') or now().date().isoformat(); exit_reason=(request.form.get('exit_reason') or '').strip() or 'Dipindahkan ke Ex Karyawan'
   st=c.execute('SELECT name FROM staff WHERE id=?',(sid,)).fetchone()
   if not st: flash('Data staf tidak ditemukan.','danger'); return redirect(url_for('former_page'))
   c.execute("UPDATE staff SET status='Ex Karyawan',exit_date=?,exit_reason=? WHERE id=?",(exit_date,exit_reason,sid)); c.execute('UPDATE users SET is_active=0 WHERE staff_id=?',(sid,)); audit(c,'former.move',f"Staf: {st['name']} · Tanggal keluar: {exit_date} · Alasan: {exit_reason}"); c.commit(); flash('Staf berhasil dipindahkan ke Ex Karyawan.','success'); return redirect(url_for('former_page'))
  rows=c.execute("SELECT s.*,o.name office_name,u.username login_id FROM staff s LEFT JOIN offices o ON o.id=s.office_id LEFT JOIN users u ON u.staff_id=s.id WHERE s.status='Ex Karyawan' ORDER BY s.name").fetchall(); active=c.execute("SELECT * FROM staff WHERE status='Aktif'").fetchall()
 return render_template('former.html',rows=rows,active=active)

@app.post('/former/<int:sid>/reactivate')
@roles('superadmin','supervisor','leader')
def former_reactivate(sid):
 with db_conn() as c:
  st=c.execute("SELECT * FROM staff WHERE id=? AND status='Ex Karyawan'",(sid,)).fetchone()
  if not st: flash('Ex Karyawan tidak ditemukan.','danger'); return redirect(url_for('former_page'))
  c.execute("UPDATE staff SET status='Aktif',exit_date=NULL,exit_reason=NULL WHERE id=?",(sid,))
  # Aktifkan kembali akun yang sudah ada dan reset ikatan device agar staf dapat login lagi.
  c.execute('UPDATE users SET is_active=1,device_token=NULL WHERE staff_id=?',(sid,))
  audit(c,'former.reactivate',f"Staf: {st['name']} · Dikembalikan menjadi Karyawan Aktif"); c.commit(); flash(f"{st['name']} berhasil dikembalikan ke Karyawan Aktif.",'success')
 return redirect(url_for('former_page'))

@app.route('/memos',methods=['GET','POST'])
@login_required
def memos_page():
 return redirect(url_for('dashboard'))

@app.get('/monitor')
@roles('superadmin','supervisor','leader')
def monitor_page():
 return redirect(url_for('reports_page'))

@app.get('/reports')
@roles('superadmin','supervisor','leader')
def reports_page():
 return redirect(url_for('leader_reports_page'))

@app.get('/staff-assignments')
@roles('superadmin','supervisor','leader')
def staff_assignments_page():
 return redirect(url_for('operations_page'))

# Deposit Monitor Sync PRO v4.2 compatible API

def authorized(): return bool(API_KEY) and request.headers.get('X-API-Key','')==API_KEY

def _monitor_settings():
 return {'enabled':True,'lateMinutes':LATE_MINUTES,'scanSeconds':SCAN_SECONDS,'leaderTtlSeconds':LEADER_TTL_SECONDS,'maxDevices':MAX_DEVICES}

def _choose_monitor_leader(c,office_id=None,ts=None):
 # Deposit Monitor V24 bersifat GLOBAL: hanya satu leader scanner untuk seluruh kantor.
 ts=int(ts or time.time()); cutoff=ts-LEADER_TTL_SECONDS
 row=c.execute('SELECT device_id FROM devices WHERE last_seen>=? ORDER BY device_id LIMIT 1',(cutoff,)).fetchone()
 return row['device_id'] if row else None

@app.get('/api/health')
def api_health():
 return jsonify(status='ok',service='omtogel-staff-deposit-sync-v24',db=DB_PATH,lateMinutes=LATE_MINUTES,scanSeconds=SCAN_SECONDS)

@app.get('/api/offices')
def api_offices():
 if not authorized(): return jsonify(ok=False,error='API key tidak valid'),401
 with db_conn() as c:
  rows=c.execute("SELECT id,name,location FROM offices WHERE status='Aktif' ORDER BY name").fetchall()
 return jsonify(ok=True,offices=[dict(x) for x in rows])

@app.post('/api/test-telegram')
def api_test_telegram():
 if not authorized(): return jsonify(ok=False,error='API key tidak valid'),401
 if not BOT_TOKEN or not ALERT_CHAT_ID: return jsonify(ok=False,error='BOT_TOKEN / ALERT_CHAT_ID belum diatur'),400
 ok=tg_send(ALERT_CHAT_ID,'✅ <b>Deposit Monitor Sync PRO</b>\nServer KENZO TIGER8008 dan Telegram terhubung.')
 return jsonify(ok=True) if ok else (jsonify(ok=False,error='Telegram gagal mengirim pesan'),502)

@app.route('/api/heartbeat',methods=['POST'])
def heartbeat():
 if not authorized():return jsonify(ok=False,error='API key tidak valid'),401
 d=request.get_json(silent=True) or {}; did=str(d.get('deviceId','')).strip(); name=str(d.get('deviceName') or 'Perangkat').strip()
 if not did:return jsonify(ok=False,error='deviceId wajib'),400
 office_id=None  # V24: extension global, kantor ditentukan dari Penugasan Kerja yang cocok.
 ts=int(time.time())
 with lock,db_conn() as c:
  old=c.execute('SELECT * FROM devices WHERE device_id=?',(did,)).fetchone()
  if not old and MAX_DEVICES>0:
   active_total=c.execute('SELECT COUNT(*) n FROM devices WHERE last_seen>=?',(ts-LEADER_TTL_SECONDS,)).fetchone()['n']
   if active_total>=MAX_DEVICES:return jsonify(ok=False,error=f'Batas perangkat online tercapai ({MAX_DEVICES})'),403
  if old:
   c.execute('UPDATE devices SET device_name=?,office_id=?,last_seen=?,page_url=?,form_count=?,late_count=? WHERE device_id=?',(name,office_id,ts,str(d.get('pageUrl') or ''),int(d.get('formCount') or 0),int(d.get('lateCount') or 0),did))
  else:
   c.execute('INSERT INTO devices(device_id,device_name,office_id,last_seen,page_url,form_count,late_count) VALUES(?,?,?,?,?,?,?)',(did,name,office_id,ts,str(d.get('pageUrl') or ''),int(d.get('formCount') or 0),int(d.get('lateCount') or 0)))
  c.execute('DELETE FROM devices WHERE last_seen<?',(ts-7*24*3600,)); c.commit(); leader=_choose_monitor_leader(c,office_id,ts)
 return jsonify(ok=True,isLeader=(leader==did),leaderDeviceId=leader,settings=_monitor_settings(),serverTimeWib=now().strftime('%Y-%m-%d %H:%M:%S'),officeId=office_id)

@app.route('/api/forms',methods=['POST'])
@app.route('/api/form-alert',methods=['POST'])
def form_alert():
 if not authorized():return jsonify(ok=False,error='API key tidak valid'),401
 d=request.get_json(silent=True) or {}; form_id=str(d.get('formId') or d.get('id') or '').strip(); device_id=str(d.get('deviceId') or '').strip()
 if not form_id:return jsonify(ok=False,error='formId wajib'),400
 if not device_id:return jsonify(ok=False,error='deviceId wajib'),400
 destination=str(d.get('destination') or d.get('bank') or d.get('target') or '').strip(); status=str(d.get('status') or 'pending').lower().strip(); last=int(time.time())
 try: age=max(0,int(float(d.get('ageMinutes') or 0)))
 except (TypeError,ValueError): age=0
 try: first=int(d.get('firstSeen') or (last-age*60))
 except (TypeError,ValueError): first=last-age*60
 done=status in ('done','processed','completed','success','approved','selesai')
 with lock,db_conn() as c:
  dev=c.execute('SELECT * FROM devices WHERE device_id=?',(device_id,)).fetchone()
  ass,map_status,expected_jobdesk=find_deposit_assignment_global(c,d,now()); sid=ass['staff_id'] if ass else None
  office_id=ass['office_id'] if ass else None
  leave=c.execute("SELECT id FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone() if sid else None; staff_status='OUT' if leave else 'Aktif'
  existing=c.execute('SELECT * FROM deposit_forms WHERE form_id=?',(form_id,)).fetchone(); processed_at=now().isoformat() if done else (existing['processed_at'] if existing else None)
  snapshot_staff=ass['staff_name'] if ass else (existing['staff_name_snapshot'] if existing else None); snapshot_cs=ass['cs_name'] if ass else (existing['cs_name_snapshot'] if existing else None); snapshot_job=ass['channel_name'] if ass else ((existing['jobdesk_snapshot'] if existing else None) or expected_jobdesk); snapshot_office=ass['office_name'] if ass else (existing['office_snapshot'] if existing else None)
  if existing:
   c.execute("""UPDATE deposit_forms SET device_id=?,office_id=COALESCE(?,office_id),username=?,game_id=?,destination=?,destination_account=?,destination_owner=?,form_time=?,amount=?,bank=?,first_seen=CASE WHEN first_seen IS NULL OR first_seen=0 OR first_seen>? THEN ? ELSE first_seen END,last_seen=?,status=?,staff_id=COALESCE(staff_id,?),assignment_id=COALESCE(assignment_id,?),staff_status=?,processed_at=?,staff_name_snapshot=COALESCE(staff_name_snapshot,?),cs_name_snapshot=COALESCE(cs_name_snapshot,?),jobdesk_snapshot=COALESCE(jobdesk_snapshot,?),office_snapshot=COALESCE(office_snapshot,?),mapping_status=?,balance_group=? WHERE id=?""",(device_id,office_id,d.get('username'),d.get('gameId'),destination,d.get('destinationAccount'),d.get('destinationOwner'),d.get('formTime'),str(d.get('amount','')),d.get('bank'),first,first,last,status,sid,ass['id'] if ass else None,staff_status,processed_at,snapshot_staff,snapshot_cs,snapshot_job,snapshot_office,map_status,d.get('balanceGroup'),existing['id']))
  else:
   c.execute("""INSERT INTO deposit_forms(form_id,device_id,office_id,username,game_id,destination,destination_account,destination_owner,form_time,amount,bank,first_seen,last_seen,status,alert_sent,staff_id,assignment_id,staff_status,processed_at,staff_name_snapshot,cs_name_snapshot,jobdesk_snapshot,office_snapshot,age_at_alert,mapping_status,balance_group) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,0,?,?,?,?,?,?,?,?,?,?,?)""",(form_id,device_id,office_id,d.get('username'),d.get('gameId'),destination,d.get('destinationAccount'),d.get('destinationOwner'),d.get('formTime'),str(d.get('amount','')),d.get('bank'),first,last,status,sid,ass['id'] if ass else None,staff_status,processed_at,snapshot_staff,snapshot_cs,snapshot_job,snapshot_office,0,map_status,d.get('balanceGroup')))
  row=c.execute('SELECT * FROM deposit_forms WHERE form_id=?',(form_id,)).fetchone()
  if done:
   c.commit(); return jsonify(ok=True,sent=False,reason='Form sudah selesai',formId=form_id,csName=snapshot_cs,staffId=sid)
  if age<LATE_MINUTES:
   c.commit(); return jsonify(ok=True,sent=False,reason='Belum lewat batas waktu',formId=form_id,ageMinutes=age)
  if row['alert_sent']:
   c.commit(); return jsonify(ok=True,sent=False,reason='Sudah pernah dikirim',formId=form_id,ageMinutes=age,staffId=row['staff_id'] or sid,csName=row['cs_name_snapshot'] or snapshot_cs,jobdesk=row['jobdesk_snapshot'] or snapshot_job,mappingStatus=row['mapping_status'] or map_status)
  c.execute('UPDATE deposit_forms SET alert_sent=1,age_at_alert=?,alerted_at=?,mapping_status=? WHERE form_id=?',(age,now().isoformat(),map_status,form_id)); c.commit()
  office_row=c.execute('SELECT name FROM offices WHERE id=?',(office_id,)).fetchone() if office_id else None; cs_name=snapshot_cs or 'BELUM DISET'; office_name=snapshot_office or (office_row['name'] if office_row else '-'); jobdesk=snapshot_job or expected_jobdesk or destination or '-'
 msg=("⚠️ <b>FORM DEPOSIT TERLAMBAT</b>\n\n"+f"👤 CS: <b>{escape(str(cs_name))}</b>\n"+f"🏢 Kantor: {escape(str(office_name))}\n"+f"💼 Jobdesk: {escape(str(jobdesk))}\n\n"+f"🆔 Member: <b>{escape(str(d.get('username') or '-'))}</b>\n"+f"🕒 Waktu Form: {escape(str(d.get('formTime') or '-'))}\n"+f"⏳ Umur Form: <b>{age} menit</b>\n"+f"💰 Amount: {escape(str(d.get('amount') or '-'))}\n"+f"🎯 Tujuan: {escape(str(destination or '-'))} - {escape(str(d.get('destinationAccount') or '-'))} - {escape(str(d.get('destinationOwner') or '-'))}")
 sent=tg_send(ALERT_CHAT_ID,msg)
 if not sent:
  with lock,db_conn() as c:
   c.execute('UPDATE deposit_forms SET alert_sent=0,alerted_at=NULL WHERE form_id=?',(form_id,)); c.commit()
  return jsonify(ok=False,error='Telegram gagal mengirim alert'),502
 return jsonify(ok=True,sent=True,reason='Terkirim',formId=form_id,ageMinutes=age,staffId=sid,csName=cs_name,jobdesk=jobdesk,mappingStatus=map_status)

@app.get('/api/status')
def api_status():
 if not authorized():return jsonify(ok=False,error='API key tidak valid'),401
 ts=int(time.time())
 with db_conn() as c:
  rows=c.execute("""SELECT d.*,o.name office_name FROM devices d LEFT JOIN offices o ON o.id=d.office_id ORDER BY d.last_seen DESC""").fetchall(); sent_count=c.execute('SELECT COUNT(*) n FROM deposit_forms WHERE alert_sent=1').fetchone()['n']; devices=[]; global_leader=_choose_monitor_leader(c,None,ts)
  for r in rows:
   item=dict(r); item['online']=bool((r['last_seen'] or 0)>=ts-LEADER_TTL_SECONDS); item['isLeader']=item['online'] and global_leader==r['device_id']; devices.append(item)
 return jsonify(ok=True,devices=devices,sentForms=sent_count,settings=_monitor_settings(),lateMinutes=LATE_MINUTES,scanSeconds=SCAN_SECONDS,serverTimeWib=now().strftime('%Y-%m-%d %H:%M:%S'))


@app.get('/staff/add')
@roles('superadmin','supervisor','leader')
def staff_add_page():
 with db_conn() as c: offices=c.execute("SELECT * FROM offices WHERE status='Aktif' ORDER BY name").fetchall()
 return render_template('staff_add.html',offices=offices)

@app.get('/leader-reports')
@roles('superadmin','supervisor','leader')
def leader_reports_page():
 # Rentang fleksibel; data operasional otomatis dibersihkan sesuai RETENTION_DAYS.
 today=now().date(); default_start=(today-timedelta(days=6)).isoformat(); default_end=today.isoformat()
 start=request.args.get('start') or default_start; end=request.args.get('end') or default_end; office_id=request.args.get('office_id',type=int); staff_id=request.args.get('staff_id',type=int)
 try:
  start_dt=datetime.fromisoformat(start+'T00:00:00').replace(tzinfo=WIB); end_dt=datetime.fromisoformat(end+'T23:59:59').replace(tzinfo=WIB)
  if end_dt<start_dt: raise ValueError
 except Exception:
  start=default_start; end=default_end; start_dt=datetime.fromisoformat(start+'T00:00:00').replace(tzinfo=WIB); end_dt=datetime.fromisoformat(end+'T23:59:59').replace(tzinfo=WIB)
 start_ts=int(start_dt.timestamp()); end_ts=int(end_dt.timestamp())+1
 with db_conn() as c:
  offices=c.execute("SELECT * FROM offices WHERE status='Aktif' ORDER BY name").fetchall(); staff=c.execute("SELECT id,name,office_id FROM staff WHERE status='Aktif' ORDER BY name").fetchall()
  clauses=[]; p=[start_ts,end_ts]
  if office_id: clauses.append('s.office_id=?'); p.append(office_id)
  if staff_id: clauses.append('s.id=?'); p.append(staff_id)
  extra_where=(' AND '+' AND '.join(clauses)) if clauses else ''
  pending=c.execute('''SELECT s.id,s.name,COALESCE(NULLIF(f.cs_name_snapshot,''),s.cs_name,'-') cs_name,COALESCE(NULLIF(f.office_snapshot,''),o.name,'-') office_name,COUNT(f.id) pending_count,MAX(CASE WHEN COALESCE(f.age_at_alert,0)>CAST((f.last_seen-f.first_seen)/60 AS INTEGER) THEN f.age_at_alert ELSE CAST((f.last_seen-f.first_seen)/60 AS INTEGER) END) max_age,ROUND(AVG(CASE WHEN COALESCE(f.age_at_alert,0)>CAST((f.last_seen-f.first_seen)/60.0 AS REAL) THEN f.age_at_alert ELSE CAST((f.last_seen-f.first_seen)/60.0 AS REAL) END),1) avg_age
    FROM deposit_forms f JOIN staff s ON s.id=f.staff_id LEFT JOIN offices o ON o.id=s.office_id
    WHERE f.alert_sent=1 AND f.first_seen>=? AND f.first_seen<?'''+extra_where+''' GROUP BY s.id ORDER BY pending_count DESC,max_age DESC,s.name''',p).fetchall()
  lp=[start_dt.isoformat(),end_dt.isoformat()]; lclauses=[]
  if office_id:lclauses.append('s.office_id=?');lp.append(office_id)
  if staff_id:lclauses.append('s.id=?');lp.append(staff_id)
  lw=(' AND '+' AND '.join(lclauses)) if lclauses else ''
  inout=c.execute('''SELECT s.id,s.name,s.cs_name,o.name office_name,COUNT(l.id) total_out,SUM(CASE WHEN l.late_minutes>0 THEN 1 ELSE 0 END) late_count,SUM(l.late_minutes) late_minutes,SUM(l.fine) total_fine,SUM(CASE WHEN l.status='OUT' THEN 1 ELSE 0 END) not_in_count
    FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.out_at>=? AND l.out_at<=?'''+lw+''' GROUP BY s.id ORDER BY late_count DESC,not_in_count DESC,total_out DESC''',lp).fetchall()
  detail_sql='''SELECT l.*,s.name,s.cs_name,o.name office_name FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.out_at>=? AND l.out_at<=? AND (l.late_minutes>0 OR l.status='AUTO_IN' OR l.auto_in=1)'''
  detail_params=[start+'T00:00:00+07:00',end+'T23:59:59+07:00']
  if office_id: detail_sql+=' AND s.office_id=?'; detail_params.append(office_id)
  if staff_id: detail_sql+=' AND s.id=?'; detail_params.append(staff_id)
  detail_sql+=' ORDER BY l.out_at DESC'; inout_details=c.execute(detail_sql,detail_params).fetchall()
  totals={'pending':sum((x['pending_count'] or 0) for x in pending),'out':sum((x['total_out'] or 0) for x in inout),'late':sum((x['late_count'] or 0) for x in inout),'fine':sum((x['total_fine'] or 0) for x in inout)}
 return render_template('leader_reports.html',pending=pending,inout=inout,inout_details=inout_details,totals=totals,offices=offices,staff=staff,start=start,end=end,office_id=office_id,staff_id=staff_id,retention_days=RETENTION_DAYS)

@app.route('/nawala',methods=['GET','POST'])
@login_required
def nawala_page():
 results=[]; raw=''
 if request.method=='POST':
  raw=request.form.get('domains',''); domains=[]
  for item in re.split(r'[\s,;]+',raw):
   d=clean_domain(item)
   if d and looks_like_domain(d) and d not in domains: domains.append(d)
   if len(domains)>=50: break
  if not domains: flash('Tidak ada domain valid.','danger')
  else:
   try:
    results=check_nawala(domains)
    if any(status=='ERROR' for _,status in results):
     flash('Sebagian hasil tidak dapat dibaca dari Nawala. Status ERROR tidak dianggap AMAN; silakan cek ulang.','danger')
   except Exception as e:
    print('[nawala]',repr(e),flush=True); results=[(d,'ERROR') for d in domains]; flash('Nawala tidak dapat dihubungi saat ini. Tidak ada domain yang dianggap AMAN tanpa hasil resmi.','danger')
 return render_template('nawala.html',results=results,raw=raw,checked_at=now() if results else None)

def clean_domain(value):
 d=(value or '').strip().lower()
 d=re.sub(r'^https?://','',d).split('/')[0].split('?')[0].split('#')[0]
 if d.startswith('www.'): d=d[4:]
 if ':' in d: d=d.split(':',1)[0]
 return d.strip('.')

def looks_like_domain(value):
 return bool(re.fullmatch(r'(?!-)[a-z0-9-]{1,63}(?<!-)(?:\.(?!-)[a-z0-9-]{1,63}(?<!-))+',clean_domain(value)))

def _nawala_status(text):
 """Konversi teks status resmi Nawala. Tidak pernah menebak AMAN bila status tidak ditemukan."""
 t=re.sub(r'\s+',' ',(text or '').strip().lower())
 if not t: return 'ERROR'
 # Frasa negatif harus dicek lebih dulu.
 if re.search(r'\b(tidak\s+ada|not\s+blocked|tidak\s+diblokir|aman|safe|clean)\b',t): return 'AMAN'
 if re.search(r'\b(blocked|diblokir|blokir|terblokir)\b',t): return 'BLOKIR'
 # UI Nawala lama menggunakan "Ada" = tercantum/terblokir dan "Tidak Ada" = aman.
 if re.fullmatch(r'.*\bada\b.*',t) and 'tidak ada' not in t: return 'BLOKIR'
 return 'ERROR'

def _parse_nawala_html_for_rows(html, requested_domains):
 soup=BeautifulSoup(html,'html.parser'); found={}
 def norm(x): return re.sub(r'\s+',' ',(x or '').strip().lower())
 # 1. Prioritas tabel hasil dengan kolom Domain/Situs dan Status/Keterangan.
 for table in soup.find_all('table'):
  first=table.find('thead') or table.find('tr')
  headers=[norm(x.get_text(' ',strip=True)) for x in first.find_all(['th','td'])] if first else []
  if not headers: continue
  try: di=next(i for i,h in enumerate(headers) if any(k in h for k in ('domain','situs','website')))
  except StopIteration: continue
  try: si=next(i for i,h in enumerate(headers) if any(k in h for k in ('status','keterangan')))
  except StopIteration: continue
  for tr in table.find_all('tr'):
   cells=tr.find_all('td')
   if len(cells)<=max(di,si): continue
   dom=clean_domain(cells[di].get_text(' ',strip=True))
   if not looks_like_domain(dom): continue
   stcell=cells[si]; badge=stcell.find(class_=re.compile(r'badge|status|label',re.I)); st=(badge or stcell).get_text(' ',strip=True)
   status=_nawala_status(st)
   if status!='ERROR': found[dom]=status
 # 2. Cari container terdekat yang memuat domain, agar tidak membaca teks status domain lain.
 for d in requested_domains:
  if d in found: continue
  node=soup.find(string=re.compile(r'(?<![a-z0-9-])'+re.escape(d)+r'(?![a-z0-9-])',re.I))
  if node:
   cur=node.parent
   for _ in range(5):
    if not cur: break
    txt=cur.get_text(' ',strip=True)
    status=_nawala_status(txt)
    if status!='ERROR': found[d]=status; break
    cur=cur.parent
 # 3. Fallback regex sangat sempit di sekitar domain. Bila tidak pasti => ERROR, bukan AMAN.
 flat=' '.join(BeautifulSoup(html,'html.parser').stripped_strings)
 for d in requested_domains:
  if d in found: continue
  m=re.search(re.escape(d)+r'.{0,180}?(tidak\s+ada|not\s+blocked|aman|safe|blocked|diblokir|blokir|terblokir|\bada\b)',flat,re.I)
  if m:
   st=_nawala_status(m.group(1))
   if st!='ERROR': found[d]=st
 return [(d,found.get(d,'ERROR')) for d in requested_domains]

def check_nawala(domains):
 """Cek langsung ke nawala.in setiap request. Tidak memakai cache hasil lokal."""
 url='https://nawala.in/'
 headers={
  'User-Agent':'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126 Safari/537.36',
  'Accept':'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
  'Accept-Language':'id-ID,id;q=0.9,en-US;q=0.8,en;q=0.7',
  'Cache-Control':'no-cache, no-store, max-age=0','Pragma':'no-cache','Referer':url,'Origin':'https://nawala.in'
 }
 sess=requests.Session(); sess.headers.update(headers)
 r=sess.get(url,timeout=25,params={'_ts':int(time.time()*1000)}); r.raise_for_status(); soup=BeautifulSoup(r.text,'html.parser')
 hidden={}
 for inp in soup.find_all('input'):
  if (inp.get('type') or '').lower()=='hidden' and inp.get('name'): hidden[inp.get('name')]=inp.get('value') or ''
 # Ikuti action form bila Nawala mengubah endpoint.
 form=None
 for f in soup.find_all('form'):
  if f.find(attrs={'name':re.compile(r'domain',re.I)}) or 'domain' in f.get_text(' ',strip=True).lower(): form=f; break
 action=(form.get('action') if form else '') or url
 if action.startswith('/'): action='https://nawala.in'+action
 elif not action.startswith('http'): action='https://nawala.in/'+action.lstrip('./')
 # Gunakan field yang dipakai source Nawala lama; hidden token ikut dikirim.
 payload={**hidden,'domains':'\n'.join(domains)}
 p=sess.post(action,data=payload,timeout=35,allow_redirects=True,headers={**headers,'Cache-Control':'no-cache, no-store, max-age=0'}); p.raise_for_status()
 rows=_parse_nawala_html_for_rows(p.text,domains)
 # Jangan pernah mengubah ERROR menjadi AMAN. Ini mencegah false-safe saat HTML berubah/Cloudflare muncul.
 return rows

@app.route('/mistakes',methods=['GET','POST'])
@login_required
def mistakes_page():
 if g.user['role']=='staff' and not menu_allowed('mistakes'): return ('Akses Catatan Mistake dinonaktifkan oleh Master.',403)
 if not g.user['staff_id']: return ('Akun ini tidak terhubung ke Data Staf.',400)
 sid=g.user['staff_id']
 with db_conn() as c:
  if request.method=='POST':
   action=(request.form.get('action') or 'save').strip()
   mid=request.form.get('id',type=int)
   if action=='delete':
    row=c.execute('SELECT * FROM mistake_ledger WHERE id=? AND staff_id=?',(mid,sid)).fetchone()
    if row:
     c.execute('DELETE FROM mistake_ledger WHERE id=? AND staff_id=?',(mid,sid)); c.commit(); flash('Catatan berhasil dihapus.','success')
    return redirect(url_for('mistakes_page'))
   entry_date=(request.form.get('entry_date') or now().date().isoformat()).strip()
   entry_type=(request.form.get('entry_type') or 'MISTAKE').upper().strip()
   if entry_type not in ('MISTAKE','POTONGAN'):
    flash('Jenis catatan tidak valid.','danger'); return redirect(url_for('mistakes_page'))
   amount=max(0,request.form.get('amount',type=int) or 0)
   title=(request.form.get('title') or '').strip()[:160]
   notes=(request.form.get('notes') or '').strip()[:1000]
   staff_note=(request.form.get('staff_note') or '').strip()[:1000]
   if amount<=0:
    flash('Nominal harus lebih dari Rp0.','danger'); return redirect(url_for('mistakes_page'))
   if mid:
    row=c.execute('SELECT id FROM mistake_ledger WHERE id=? AND staff_id=?',(mid,sid)).fetchone()
    if not row:
     flash('Catatan tidak ditemukan.','danger'); return redirect(url_for('mistakes_page'))
    c.execute('UPDATE mistake_ledger SET entry_date=?,entry_type=?,amount=?,title=?,notes=?,staff_note=?,updated_at=? WHERE id=? AND staff_id=?',(entry_date,entry_type,amount,title,notes,staff_note,now().isoformat(),mid,sid))
    flash('Catatan pribadi berhasil diperbarui.','success')
   else:
    c.execute('INSERT INTO mistake_ledger(staff_id,entry_date,entry_type,amount,title,notes,staff_note,created_by,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?,?)',(sid,entry_date,entry_type,amount,title,notes,staff_note,g.user['id'],now().isoformat(),now().isoformat()))
    flash('Catatan pribadi berhasil ditambahkan.','success')
   c.commit(); return redirect(url_for('mistakes_page'))
  rows=c.execute('SELECT * FROM mistake_ledger WHERE staff_id=? ORDER BY entry_date DESC,id DESC',(sid,)).fetchall()
  total_mistake=sum(r['amount'] for r in rows if r['entry_type']=='MISTAKE'); total_cut=sum(r['amount'] for r in rows if r['entry_type']=='POTONGAN'); remaining=max(0,total_mistake-total_cut)
 return render_template('mistakes.html',rows=rows,total_mistake=total_mistake,total_cut=total_cut,remaining=remaining,today=now().date().isoformat())

@app.post('/mistakes/<int:mid>/delete')
@login_required
def mistake_self_delete(mid):
 if not g.user['staff_id']: return ('Akses ditolak',403)
 with db_conn() as c:
  row=c.execute('SELECT id FROM mistake_ledger WHERE id=? AND staff_id=?',(mid,g.user['staff_id'])).fetchone()
  if row:
   c.execute('DELETE FROM mistake_ledger WHERE id=? AND staff_id=?',(mid,g.user['staff_id'])); c.commit(); flash('Catatan pribadi berhasil dihapus.','success')
 return redirect(url_for('mistakes_page'))

@app.route('/mistakes/manage',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def mistakes_manage_page():
 return ('Catatan Mistake adalah catatan pribadi masing-masing staf dan tidak dikelola Leader/Master.',403)

@app.post('/mistakes/manage/<int:mid>/delete')
@roles('superadmin','supervisor','leader')
def mistake_delete(mid):
 return ('Catatan Mistake adalah catatan pribadi masing-masing staf dan tidak dapat dihapus Leader/Master.',403)

@app.get('/history')
@login_required
def my_history_page():
 if g.user['role']=='staff' and not menu_allowed('history'): return ('Akses History Saya dinonaktifkan oleh Master.',403)
 sid=g.user['staff_id']
 if not sid:return ('Akun tidak terhubung ke staf.',400)
 cutoff=now()-timedelta(days=RETENTION_DAYS); start_ts=int(cutoff.timestamp()); month_start=now().replace(day=1,hour=0,minute=0,second=0,microsecond=0)
 with db_conn() as c:
  sp=c.execute('SELECT * FROM warnings WHERE staff_id=? ORDER BY warning_date DESC,id DESC',(sid,)).fetchall(); leaves=c.execute('SELECT * FROM leaves WHERE staff_id=? AND out_at>=? ORDER BY out_at DESC',(sid,month_start.isoformat())).fetchall(); pending=c.execute('SELECT * FROM deposit_forms WHERE staff_id=? AND alert_sent=1 AND first_seen>=? ORDER BY first_seen DESC',(sid,start_ts)).fetchall(); mistakes=c.execute('SELECT * FROM mistake_ledger WHERE staff_id=? ORDER BY entry_date DESC,id DESC',(sid,)).fetchall()
  summary={'sp':len(sp),'pending':len(pending),'late_inout':sum(1 for x in leaves if (x['late_minutes'] or 0)>0),'fine':sum((x['fine'] or 0) for x in leaves),'mistake':sum(x['amount'] for x in mistakes if x['entry_type']=='MISTAKE'),'cut':sum(x['amount'] for x in mistakes if x['entry_type']=='POTONGAN')}
 return render_template('history.html',sp=sp,leaves=leaves,pending=pending,mistakes=mistakes,summary=summary,retention_days=RETENTION_DAYS,inout_month=month_start.strftime('%B %Y'))

@app.get('/login-logs')
@roles('superadmin','supervisor','leader')
def login_logs_page():
 event=request.args.get('event',''); q=(request.args.get('q') or '').strip(); office_id=request.args.get('office_id',type=int)
 with db_conn() as c:
  sql='''SELECT l.*,u.username,s.name staff_name,o.name office_name FROM login_logs l LEFT JOIN users u ON u.id=l.user_id LEFT JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE 1=1'''; p=[]
  if event:sql+=' AND l.event=?';p.append(event)
  if q:sql+=' AND (lower(u.username) LIKE ? OR lower(s.name) LIKE ?)';p.extend([f'%{q.lower()}%',f'%{q.lower()}%'])
  if office_id:sql+=' AND s.office_id=?';p.append(office_id)
  sql+=' ORDER BY l.id DESC LIMIT 1000'; rows=c.execute(sql,p).fetchall(); offices=c.execute('SELECT * FROM offices ORDER BY name').fetchall()
 return render_template('login_logs.html',rows=rows,offices=offices,event=event,q=q,office_id=office_id)

@app.get('/account/theme/<mode>')
@login_required
def set_theme(mode):
 if mode not in ('dark','light'):return redirect(url_for('account_page'))
 session['theme']=mode;return redirect(request.referrer or url_for('account_page'))

@app.get('/cek-nawala-coming-soon')
@login_required
def cek_nawala_legacy(): return redirect(url_for('nawala_page'))

@app.errorhandler(sqlite3.IntegrityError)
def handle_integrity_error(error):
 print('[integrity]', error, flush=True)
 if request.method=='POST':
  flash('Data tidak dapat disimpan karena ada nilai yang sama atau relasi data belum lengkap. Periksa kembali isian.','danger')
  return redirect(request.referrer or url_for('dashboard'))
 return ('Data tidak valid',400)

@app.errorhandler(sqlite3.OperationalError)
def handle_operational_error(error):
 print('[sqlite operational]', error, flush=True)
 return render_template('error.html', message='Database sedang bermasalah. Silakan muat ulang halaman atau hubungi Master.'),500

def background():
 last_cleanup_day=None
 while True:
  try:
   with db_conn() as c:
    # AUTO IN diproses juga di background, tetapi request/API memiliki fallback yang sama.
    current=now()
    auto_events=process_auto_in_overdue(c,current)
    c.commit()
    flush_auto_in_notifications(auto_events)
    today_key=now().date().isoformat()
    if last_cleanup_day!=today_key:
     # Backup harian SQLite sebelum cleanup/migrasi operasional. Simpan 14 backup terbaru.
     try:
      backup_dir=os.path.join(os.path.dirname(DB_PATH) or '.', 'backups'); os.makedirs(backup_dir,exist_ok=True)
      backup_path=os.path.join(backup_dir,f'omtogel_staff_{today_key}.db')
      if not os.path.exists(backup_path):
       dst=sqlite3.connect(backup_path); c.backup(dst); dst.close()
      backups=sorted([os.path.join(backup_dir,x) for x in os.listdir(backup_dir) if x.startswith('omtogel_staff_') and x.endswith('.db')])
      for old_backup in backups[:-14]:
       try: os.remove(old_backup)
       except OSError: pass
     except Exception as be: print('[backup]',be,flush=True)
     cutoff_dt=now()-timedelta(days=RETENTION_DAYS); cutoff_ts=int(cutoff_dt.timestamp()); cutoff_iso=cutoff_dt.isoformat()
     c.execute('DELETE FROM deposit_forms WHERE first_seen>0 AND first_seen<?',(cutoff_ts,))
     c.execute('DELETE FROM leaves WHERE out_at<?',(cutoff_iso,)); c.execute('DELETE FROM login_logs WHERE created_at<?',(cutoff_iso,))
     c.execute('INSERT INTO audit_logs(user_id,action,detail,created_at) VALUES(NULL,?,?,?)',('retention.cleanup',f'older_than={RETENTION_DAYS}d',now().isoformat()))
     last_cleanup_day=today_key
    c.commit()
  except Exception as e:print('[background]',e,flush=True)
  time.sleep(2)
def start_bg():
 global bg_started
 if not bg_started:bg_started=True;threading.Thread(target=background,daemon=True).start()

init_db();start_bg();print('[startup] SQLite database:',DB_PATH,flush=True)
if __name__=='__main__':app.run(host='0.0.0.0',port=int(os.getenv('PORT','8080')))
