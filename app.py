import os, json, time, sqlite3, threading, secrets, re, uuid, shutil
from datetime import datetime, timedelta
from functools import wraps
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

def init_db():
  with lock,db_conn() as c:
    c.executescript('''
    CREATE TABLE IF NOT EXISTS offices(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT UNIQUE NOT NULL,location TEXT,status TEXT DEFAULT 'Aktif');
    CREATE TABLE IF NOT EXISTS staff(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT NOT NULL,telegram_id TEXT UNIQUE,telegram_username TEXT,email TEXT,agent_code TEXT,cs_name TEXT,office_id INTEGER,position TEXT DEFAULT 'CS',status TEXT DEFAULT 'Aktif',join_date TEXT,exit_date TEXT,exit_reason TEXT,notes TEXT,FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY AUTOINCREMENT,username TEXT UNIQUE NOT NULL,password_hash TEXT NOT NULL,role TEXT DEFAULT 'staff',staff_id INTEGER UNIQUE,office_id INTEGER,is_active INTEGER DEFAULT 1,must_change_password INTEGER DEFAULT 1,allowed_menus TEXT DEFAULT '["my_dashboard","inout","nawala","mistakes","history","account"]',device_token TEXT,last_login TEXT,twofa_secret TEXT,twofa_enabled INTEGER DEFAULT 0,FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS shifts(id INTEGER PRIMARY KEY AUTOINCREMENT,office_id INTEGER,name TEXT NOT NULL,code TEXT,start_time TEXT,end_time TEXT,status TEXT DEFAULT 'Aktif',UNIQUE(office_id,name),FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS shift_schedules(id INTEGER PRIMARY KEY AUTOINCREMENT,work_date TEXT NOT NULL,staff_id INTEGER NOT NULL,shift_id INTEGER NOT NULL,office_id INTEGER NOT NULL,UNIQUE(work_date,staff_id),FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(shift_id) REFERENCES shifts(id),FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS channels(id INTEGER PRIMARY KEY AUTOINCREMENT,office_id INTEGER,name TEXT NOT NULL,category TEXT NOT NULL,aliases TEXT DEFAULT '',status TEXT DEFAULT 'Aktif',UNIQUE(office_id,name),FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS assignments(id INTEGER PRIMARY KEY AUTOINCREMENT,assignment_batch_id TEXT,work_date TEXT NOT NULL,office_id INTEGER,shift_id INTEGER,staff_id INTEGER,channel_id INTEGER,category TEXT,target TEXT,start_time TEXT,end_time TEXT,is_active INTEGER DEFAULT 1,FOREIGN KEY(office_id) REFERENCES offices(id),FOREIGN KEY(shift_id) REFERENCES shifts(id),FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(channel_id) REFERENCES channels(id));
    CREATE TABLE IF NOT EXISTS offdays(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,off_date TEXT,notes TEXT,created_at TEXT,UNIQUE(staff_id,off_date),FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS leaves(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER NOT NULL,reason TEXT,out_at TEXT,expected_at TEXT,in_at TEXT,status TEXT DEFAULT 'OUT',late_minutes INTEGER DEFAULT 0,fine INTEGER DEFAULT 0,source TEXT,notified_overdue INTEGER DEFAULT 0,assignment_snapshot TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS warnings(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,type TEXT,warning_date TEXT,reason TEXT,fine INTEGER DEFAULT 0,notes TEXT,created_by INTEGER,created_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS memos(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,title TEXT,category TEXT,body TEXT,priority TEXT DEFAULT 'Normal',status TEXT DEFAULT 'Baru',leader_reply TEXT,created_at TEXT,updated_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS devices(device_id TEXT PRIMARY KEY,device_name TEXT,office_id INTEGER,last_seen INTEGER,page_url TEXT,form_count INTEGER DEFAULT 0,late_count INTEGER DEFAULT 0,FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS deposit_forms(id INTEGER PRIMARY KEY AUTOINCREMENT,form_id TEXT UNIQUE,device_id TEXT,office_id INTEGER,username TEXT,game_id TEXT,destination TEXT,destination_account TEXT,destination_owner TEXT,form_time TEXT,amount TEXT,bank TEXT,first_seen INTEGER,last_seen INTEGER,status TEXT DEFAULT 'pending',alert_sent INTEGER DEFAULT 0,staff_id INTEGER,assignment_id INTEGER,staff_status TEXT,processed_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
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
      'leaves': [('staff_id','INTEGER'),('reason','TEXT'),('out_at','TEXT'),('expected_at','TEXT'),('in_at','TEXT'),('status',"TEXT DEFAULT 'OUT'"),('late_minutes','INTEGER DEFAULT 0'),('fine','INTEGER DEFAULT 0'),('source','TEXT'),('notified_overdue','INTEGER DEFAULT 0'),('assignment_snapshot','TEXT')],
      'warnings': [('staff_id','INTEGER'),('type','TEXT'),('warning_date','TEXT'),('reason','TEXT'),('fine','INTEGER DEFAULT 0'),('notes','TEXT'),('created_by','INTEGER'),('created_at','TEXT')],
      'memos': [('staff_id','INTEGER'),('title','TEXT'),('category','TEXT'),('body','TEXT'),('priority',"TEXT DEFAULT 'Normal'"),('status',"TEXT DEFAULT 'Baru'"),('leader_reply','TEXT'),('created_at','TEXT'),('updated_at','TEXT')],
      'devices': [('device_name','TEXT'),('office_id','INTEGER'),('last_seen','INTEGER'),('page_url','TEXT'),('form_count','INTEGER DEFAULT 0'),('late_count','INTEGER DEFAULT 0')],
      'deposit_forms': [('device_id','TEXT'),('office_id','INTEGER'),('username','TEXT'),('game_id','TEXT'),('destination','TEXT'),('destination_account','TEXT'),('destination_owner','TEXT'),('form_time','TEXT'),('amount','TEXT'),('bank','TEXT'),('first_seen','INTEGER'),('last_seen','INTEGER'),('status',"TEXT DEFAULT 'pending'"),('alert_sent','INTEGER DEFAULT 0'),('staff_id','INTEGER'),('assignment_id','INTEGER'),('staff_status','TEXT'),('processed_at','TEXT')],
      'audit_logs': [('user_id','INTEGER'),('action','TEXT'),('detail','TEXT'),('created_at','TEXT')],
    }
    for table, columns in migrations.items():
      for name, decl in columns:
        addcol(c, table, name, decl)
    # Fill safe defaults for rows originating from legacy schemas.
    c.execute("UPDATE shifts SET code=COALESCE(NULLIF(code,''), 'SHIFT-' || id), status=COALESCE(NULLIF(status,''),'Aktif')")
    c.execute("UPDATE offices SET status=COALESCE(NULLIF(status,''),'Aktif')")
    if not c.execute("SELECT 1 FROM offices WHERE name='Kantor Utama' LIMIT 1").fetchone(): c.execute("INSERT INTO offices(name,location,status) VALUES('Kantor Utama','-','Aktif')")
    oid=c.execute('SELECT id FROM offices ORDER BY id LIMIT 1').fetchone()[0]
    # Jangan bergantung pada UNIQUE constraint database lama; cek manual supaya startup tidak membuat shift duplikat.
    if not c.execute('SELECT 1 FROM shifts WHERE office_id=? AND name=? LIMIT 1',(oid,'Pagi')).fetchone(): c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(?,?,?,?,?,?)',(oid,'Pagi','P1','06:00','18:00','Aktif'))
    if not c.execute('SELECT 1 FROM shifts WHERE office_id=? AND name=? LIMIT 1',(oid,'Malam')).fetchone(): c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(?,?,?,?,?,?)',(oid,'Malam','M1','18:00','06:00','Aktif'))
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

@app.before_request
def before():
 g.user=None; g.policy_pending=False; g.theme=session.get('theme','dark')
 if session.get('uid'):
  with db_conn() as c:
   g.user=c.execute('SELECT * FROM users WHERE id=? AND is_active=1',(session['uid'],)).fetchone()
   g.allowed_menus=[]
   if g.user:
    try:g.allowed_menus=json.loads(g.user['allowed_menus'] or '[]')
    except Exception:g.allowed_menus=[]
   if g.user and g.user['role'] in ('staff','supervisor'):
    g.policy_pending=bool(session.get('policy_pending'))

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
 for s in c.execute("SELECT * FROM shifts WHERE office_id=? AND status='Aktif'",(office_id,)):
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

@app.route('/login',methods=['GET','POST'])
def login():
 if request.method=='POST':
  with db_conn() as c:
   u=c.execute('SELECT * FROM users WHERE username=? AND is_active=1',(request.form['username'].strip(),)).fetchone()
   if not u or not check_password_hash(u['password_hash'],request.form['password']): flash('ID atau password salah.','danger'); return render_template('login.html')
   if u['role']=='staff' and any(x in request.headers.get('User-Agent','').lower() for x in ['android','iphone','ipad','mobile']): flash('Akun staf hanya dapat login dari PC.','danger'); return render_template('login.html')
   if u['twofa_enabled']:
    session['pending_uid']=u['id']; return redirect(url_for('twofa_verify'))
   if u['role']=='superadmin':
    session['uid']=u['id']; session['policy_pending']=True; c.execute('UPDATE users SET last_login=? WHERE id=?',(now().isoformat(),u['id'])); c.commit(); flash('Master wajib mengaktifkan 2FA sebelum melanjutkan.','danger'); return redirect(url_for('twofa_setup'))
   session['uid']=u['id']; session['policy_pending']=True; c.execute('UPDATE users SET last_login=? WHERE id=?',(now().isoformat(),u['id'])); c.execute('INSERT INTO login_logs(user_id,staff_id,event,ip_address,user_agent,detail,created_at) VALUES(?,?,?,?,?,?,?)',(u['id'],u['staff_id'],'LOGIN',request.headers.get('X-Forwarded-For',request.remote_addr),request.headers.get('User-Agent','')[:500],'Login berhasil',now().isoformat())); c.commit(); return redirect(url_for('dashboard'))
 return render_template('login.html')
@app.route('/2fa/verify',methods=['GET','POST'])
def twofa_verify():
 uid=session.get('pending_uid')
 if not uid:return redirect(url_for('login'))
 with db_conn() as c:u=c.execute('SELECT * FROM users WHERE id=?',(uid,)).fetchone()
 if request.method=='POST':
  if totp_verify(u['twofa_secret'],request.form['code'].strip()):
   session.pop('pending_uid',None); session['uid']=uid; session['policy_pending']=True
   with db_conn() as c2: c2.execute('INSERT INTO login_logs(user_id,staff_id,event,ip_address,user_agent,detail,created_at) VALUES(?,?,?,?,?,?,?)',(u['id'],u['staff_id'],'LOGIN',request.headers.get('X-Forwarded-For',request.remote_addr),request.headers.get('User-Agent','')[:500],'Login 2FA berhasil',now().isoformat())); c2.commit()
   return redirect(url_for('dashboard'))
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
  used=any(c.execute(q,(oid,)).fetchone() for q in ['SELECT 1 FROM staff WHERE office_id=? LIMIT 1','SELECT 1 FROM users WHERE office_id=? LIMIT 1','SELECT 1 FROM assignments WHERE office_id=? LIMIT 1','SELECT 1 FROM shifts WHERE office_id=? LIMIT 1','SELECT 1 FROM shift_schedules WHERE office_id=? LIMIT 1','SELECT 1 FROM channels WHERE office_id=? LIMIT 1','SELECT 1 FROM devices WHERE office_id=? LIMIT 1','SELECT 1 FROM deposit_forms WHERE office_id=? LIMIT 1'])
  if used: c.execute("UPDATE offices SET status='Nonaktif' WHERE id=?",(oid,)); flash('Kantor sudah memiliki data terkait, jadi dinonaktifkan.','success')
  else: c.execute('DELETE FROM offices WHERE id=?',(oid,)); flash('Kantor berhasil dihapus.','success')
  c.commit()
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
   if f.get('login_id'):
    login_id=f['login_id'].strip(); existing_user=c.execute('SELECT id FROM users WHERE staff_id=?',(sid,)).fetchone(); username_owner=c.execute('SELECT id,staff_id FROM users WHERE username=?',(login_id,)).fetchone()
    if username_owner and (not existing_user or username_owner['id']!=existing_user['id']):
     c.rollback(); flash('ID login sudah dipakai akun lain.','danger'); return redirect(url_for('staff_page'))
    if existing_user:
     if f.get('password'): c.execute('UPDATE users SET username=?,password_hash=?,office_id=?,is_active=1,must_change_password=1 WHERE id=?',(login_id,generate_password_hash(f['password']),f.get('office_id',type=int),existing_user['id']))
     else: c.execute('UPDATE users SET username=?,office_id=?,is_active=1 WHERE id=?',(login_id,f.get('office_id',type=int),existing_user['id']))
    else:
     pw=f.get('password') or secrets.token_urlsafe(6); c.execute('INSERT INTO users(username,password_hash,role,staff_id,office_id,is_active,must_change_password,allowed_menus) VALUES(?,?,?,?,?,1,1,?)',(login_id,generate_password_hash(pw),'staff',sid,f.get('office_id',type=int),json.dumps(['my_dashboard','inout','nawala','mistakes','history','account'])))
   audit(c,'staff.save',f'id={sid}'); c.commit(); flash('Data staf tersimpan.','success'); return redirect(url_for('staff_page'))
  report_date=request.args.get('date') or now().date().isoformat()
  rows=c.execute('''SELECT s.*,o.name office_name,u.username login_id,u.is_active account_active,
    ss.shift_id,sh.name shift_name,sh.start_time shift_start,sh.end_time shift_end
    FROM staff s LEFT JOIN offices o ON o.id=s.office_id LEFT JOIN users u ON u.staff_id=s.id
    LEFT JOIN shift_schedules ss ON ss.staff_id=s.id AND ss.work_date='CURRENT'
    LEFT JOIN shifts sh ON sh.id=ss.shift_id
    WHERE s.status NOT IN ('Ex Karyawan','Resign')
    ORDER BY CASE WHEN s.status="Aktif" THEN 0 ELSE 1 END,o.name,s.name''').fetchall()
  offices=c.execute('SELECT * FROM offices ORDER BY name').fetchall()
  active_rows=[r for r in rows if r['status']=='Aktif']
  office_counts=[]
  for o in offices:
   members=[r for r in active_rows if r['office_id']==o['id']]
   all_members=[r for r in rows if r['office_id']==o['id']]
   office_counts.append({'id':o['id'],'name':o['name'],'location':o['location'],'count':len(members),'all_count':len(all_members)})
  shift_counts=c.execute('''SELECT sh.id,sh.name,sh.start_time,sh.end_time,o.name office_name,COUNT(DISTINCT ss.staff_id) total
    FROM shift_schedules ss JOIN shifts sh ON sh.id=ss.shift_id JOIN offices o ON o.id=ss.office_id JOIN staff s ON s.id=ss.staff_id
    WHERE ss.work_date='CURRENT' AND s.status='Aktif' GROUP BY sh.id,sh.name,sh.start_time,sh.end_time,o.name ORDER BY o.name,sh.start_time''').fetchall()
  ex_count=c.execute("SELECT COUNT(*) n FROM staff WHERE status IN ('Ex Karyawan','Resign')").fetchone()['n']; totals={'all':len(rows)+ex_count,'active':len(active_rows),'ex':ex_count,'scheduled':sum(int(x['total']) for x in shift_counts)}
 return render_template('staff.html',rows=rows,offices=offices,office_counts=office_counts,shift_counts=shift_counts,totals=totals,report_date=report_date)

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
  audit(c,'staff.delete_or_archive',f'id={sid}'); c.commit()
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
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; action=(f.get('action') or '').strip(); work_date='CURRENT'; office_id=f.get('office_id',type=int)
   try:
    if action=='shift_save':
     sid=f.get('shift_id',type=int); vals=(office_id,(f.get('name') or '').strip(),(f.get('code') or '').strip(),f.get('start_time') or '',f.get('end_time') or '',f.get('status') or 'Aktif')
     if not vals[0] or not vals[1] or not vals[3] or not vals[4]: raise ValueError('Kantor, nama shift, jam mulai, dan jam selesai wajib diisi.')
     if sid:
      c.execute('UPDATE shifts SET office_id=?,name=?,code=?,start_time=?,end_time=?,status=? WHERE id=?',vals+(sid,)); audit(c,'operations.shift.update',f'id={sid}')
     else:
      c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(?,?,?,?,?,?)',vals); audit(c,'operations.shift.create',vals[1])
     c.commit(); flash('Jadwal shift berhasil disimpan.','success')
    elif action=='shift_delete':
     sid=f.get('shift_id',type=int)
     used=c.execute('SELECT 1 FROM assignments WHERE shift_id=? LIMIT 1',(sid,)).fetchone() or c.execute('SELECT 1 FROM shift_schedules WHERE shift_id=? LIMIT 1',(sid,)).fetchone()
     if used: c.execute("UPDATE shifts SET status='Nonaktif' WHERE id=?",(sid,)); flash('Shift sudah pernah dipakai, jadi dinonaktifkan agar riwayat tetap aman.','success')
     else: c.execute('DELETE FROM shifts WHERE id=?',(sid,)); flash('Shift berhasil dihapus.','success')
     audit(c,'operations.shift.delete_or_disable',str(sid)); c.commit()
    elif action=='copy_schedule':
     source_date=(f.get('source_date') or '').strip()
     if not source_date: raise ValueError('Tanggal sumber wajib dipilih.')
     source=c.execute('''SELECT a.* FROM assignments a WHERE a.work_date=? AND a.office_id=? AND a.is_active=1 ORDER BY a.id''',(source_date,office_id)).fetchall()
     if not source: raise ValueError('Tidak ada jadwal pada tanggal sumber untuk kantor ini.')
     # Ganti jadwal target kantor ini agar hasil copy bersih dan tidak bertumpuk.
     target_staff=[r['staff_id'] for r in c.execute('SELECT staff_id FROM shift_schedules WHERE work_date=? AND office_id=?',(work_date,office_id)).fetchall()]
     c.execute('DELETE FROM assignments WHERE work_date=? AND office_id=?',(work_date,office_id)); c.execute('DELETE FROM shift_schedules WHERE work_date=? AND office_id=?',(work_date,office_id))
     by_staff={}
     for r in source: by_staff.setdefault(r['staff_id'],[]).append(r)
     copied=0
     for staff_id,items in by_staff.items():
      st=c.execute("SELECT * FROM staff WHERE id=? AND status='Aktif' AND office_id=?",(staff_id,office_id)).fetchone()
      if not st: continue
      sh=c.execute("SELECT * FROM shifts WHERE id=? AND status='Aktif'",(items[0]['shift_id'],)).fetchone()
      if not sh: continue
      c.execute('INSERT OR REPLACE INTO shift_schedules(work_date,staff_id,shift_id,office_id) VALUES(?,?,?,?)',(work_date,staff_id,sh['id'],office_id))
      batch=uuid.uuid4().hex
      for r in items:
       c.execute('''INSERT INTO assignments(assignment_batch_id,work_date,office_id,shift_id,staff_id,channel_id,category,target,start_time,end_time,is_active) VALUES(?,?,?,?,?,?,?,?,?,?,1)''',(batch,work_date,office_id,sh['id'],staff_id,r['channel_id'],r['category'],r['target'],r['start_time'],r['end_time']))
      copied+=1
     audit(c,'operations.copy_schedule',f'from={source_date} to={work_date} office={office_id} staff={copied}'); c.commit(); flash(f'Jadwal berhasil disalin untuk {copied} staf.','success')
    elif action=='swap_staff':
     staff_a=f.get('staff_a',type=int); staff_b=f.get('staff_b',type=int)
     if not staff_a or not staff_b or staff_a==staff_b: raise ValueError('Pilih dua staf yang berbeda untuk ditukar.')
     a=c.execute('SELECT * FROM shift_schedules WHERE work_date=? AND office_id=? AND staff_id=?',(work_date,office_id,staff_a)).fetchone(); b=c.execute('SELECT * FROM shift_schedules WHERE work_date=? AND office_id=? AND staff_id=?',(work_date,office_id,staff_b)).fetchone()
     if not a or not b: raise ValueError('Kedua staf harus sudah memiliki jadwal pada tanggal ini.')
     # Tukar shift + seluruh jobdesk menggunakan placeholder staff id sementara yang tidak mungkin valid pada assignment karena FK.
     aj=c.execute('SELECT * FROM assignments WHERE work_date=? AND office_id=? AND staff_id=?',(work_date,office_id,staff_a)).fetchall(); bj=c.execute('SELECT * FROM assignments WHERE work_date=? AND office_id=? AND staff_id=?',(work_date,office_id,staff_b)).fetchall()
     c.execute('DELETE FROM assignments WHERE work_date=? AND office_id=? AND staff_id IN (?,?)',(work_date,office_id,staff_a,staff_b))
     c.execute('UPDATE shift_schedules SET shift_id=? WHERE id=?',(b['shift_id'],a['id'])); c.execute('UPDATE shift_schedules SET shift_id=? WHERE id=?',(a['shift_id'],b['id']))
     for new_staff,src,new_shift in ((staff_a,bj,b['shift_id']),(staff_b,aj,a['shift_id'])):
      batch=uuid.uuid4().hex
      for r in src:
       c.execute('''INSERT INTO assignments(assignment_batch_id,work_date,office_id,shift_id,staff_id,channel_id,category,target,start_time,end_time,is_active) VALUES(?,?,?,?,?,?,?,?,?,?,1)''',(batch,work_date,office_id,new_shift,new_staff,r['channel_id'],r['category'],r['target'],r['start_time'],r['end_time']))
     audit(c,'operations.swap_staff',f'date={work_date} office={office_id} a={staff_a} b={staff_b}'); c.commit(); flash('Shift dan seluruh jobdesk kedua staf berhasil ditukar.','success')
    elif action=='assignment_delete':
     batch_id=(f.get('batch_id') or '').strip(); staff_id=f.get('staff_id',type=int)
     if batch_id and not batch_id.startswith('legacy-'): c.execute('DELETE FROM assignments WHERE assignment_batch_id=?',(batch_id,))
     elif f.get('legacy_id',type=int): c.execute('DELETE FROM assignments WHERE id=?',(f.get('legacy_id',type=int),))
     if staff_id and not c.execute('SELECT 1 FROM assignments WHERE work_date=? AND staff_id=? LIMIT 1',(work_date,staff_id)).fetchone(): c.execute('DELETE FROM shift_schedules WHERE work_date=? AND staff_id=?',(work_date,staff_id))
     audit(c,'operations.assignment.delete',f'date={work_date} staff={staff_id}'); c.commit(); flash('Penugasan staf berhasil dihapus.','success')
    elif action=='assignment_save':
     staff_id=f.get('staff_id',type=int); shift_id=f.get('shift_id',type=int); batch_id=(f.get('batch_id') or '').strip(); legacy_id=f.get('legacy_id',type=int)
     channel_ids=[]
     for raw in f.getlist('channel_ids'):
      try:
       cid=int(raw)
       if cid not in channel_ids: channel_ids.append(cid)
      except (TypeError,ValueError): pass
     if not 1<=len(channel_ids)<=10: raise ValueError('Pilih minimal 1 dan maksimal 10 jobdesk.')
     st=c.execute("SELECT * FROM staff WHERE id=? AND status='Aktif'",(staff_id,)).fetchone(); sh=c.execute("SELECT * FROM shifts WHERE id=? AND status='Aktif'",(shift_id,)).fetchone()
     if not st or not sh: raise ValueError('Staf atau shift tidak valid.')
     if int(st['office_id'] or 0)!=int(office_id or 0) or int(sh['office_id'] or 0)!=int(office_id or 0): raise ValueError('Staf dan shift harus berasal dari kantor yang sama.')
     valid=[]
     for cid in channel_ids:
      ch=c.execute("SELECT * FROM channels WHERE id=? AND status='Aktif'",(cid,)).fetchone()
      if ch: valid.append(ch)
     if len(valid)!=len(channel_ids): raise ValueError('Ada jenis jobdesk yang tidak aktif atau tidak ditemukan.')
     # Deteksi jobdesk ganda pada shift yang sama. Tidak memblokir karena beberapa jobdesk (mis. Livechat) memang bisa dibagi.
     conflicts=[]
     for ch in valid:
      hit=c.execute('''SELECT s.name FROM assignments a JOIN staff s ON s.id=a.staff_id WHERE a.work_date=? AND a.office_id=? AND a.shift_id=? AND a.channel_id=? AND a.staff_id!=? AND a.is_active=1 LIMIT 1''',(work_date,office_id,shift_id,ch['id'],staff_id)).fetchone()
      if hit: conflicts.append(f"{ch['name']} juga dipegang {hit['name']}")
     existing_sched=c.execute('SELECT id FROM shift_schedules WHERE work_date=? AND staff_id=?',(work_date,staff_id)).fetchone()
     if existing_sched: c.execute('UPDATE shift_schedules SET shift_id=?,office_id=? WHERE id=?',(shift_id,office_id,existing_sched['id']))
     else: c.execute('INSERT INTO shift_schedules(work_date,staff_id,shift_id,office_id) VALUES(?,?,?,?)',(work_date,staff_id,shift_id,office_id))
     c.execute('DELETE FROM assignments WHERE work_date=? AND staff_id=?',(work_date,staff_id))
     batch_id=uuid.uuid4().hex
     start=f.get('start_time') or sh['start_time']; end=f.get('end_time') or sh['end_time']
     for ch in valid:
      c.execute('INSERT INTO assignments(assignment_batch_id,work_date,office_id,shift_id,staff_id,channel_id,category,target,start_time,end_time,is_active) VALUES(?,?,?,?,?,?,?,?,?,?,1)',(batch_id,work_date,office_id,shift_id,staff_id,ch['id'],ch['category'],ch['name'],start,end))
     audit(c,'operations.assignment.save',f'date={work_date} staff={staff_id} shift={shift_id} jobs={[x["id"] for x in valid]}'); c.commit(); flash('Jadwal staf dan jobdesk berhasil disimpan.','success')
     if conflicts: flash('Peringatan bentrok: ' + '; '.join(conflicts[:5]),'danger')
    else: raise ValueError('Aksi tidak dikenal.')
   except sqlite3.IntegrityError:
    c.rollback(); flash('Data bentrok dengan data yang sudah ada. Periksa nama shift atau penugasan staf.','danger')
   except ValueError as e:
    c.rollback(); flash(str(e),'danger')
   return redirect(url_for('operations_page',date=work_date,office_id=office_id or ''))
  date='CURRENT'; office_id=request.args.get('office_id',type=int)
  offices=c.execute("SELECT * FROM offices WHERE status='Aktif' ORDER BY name").fetchall()
  if not office_id and offices: office_id=offices[0]['id']
  shifts=c.execute("SELECT * FROM shifts WHERE office_id=? ORDER BY CASE WHEN status='Aktif' THEN 0 ELSE 1 END,start_time,name",(office_id,)).fetchall() if office_id else []
  staff=c.execute("SELECT * FROM staff WHERE office_id=? AND status='Aktif' ORDER BY name",(office_id,)).fetchall() if office_id else []
  channels=c.execute("SELECT * FROM channels WHERE status='Aktif' ORDER BY CASE category WHEN 'Deposit' THEN 1 WHEN 'Withdraw' THEN 2 WHEN 'Livechat' THEN 3 WHEN 'Pulsa' THEN 4 WHEN 'QRIS' THEN 5 ELSE 6 END,name").fetchall()
  raw=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,s.email,sh.name shift_name,sh.code shift_code,sh.start_time shift_start,sh.end_time shift_end,ch.name channel_name,ch.category channel_category
    FROM assignments a JOIN staff s ON s.id=a.staff_id JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id
    WHERE a.work_date=? AND a.office_id=? AND a.is_active=1 ORDER BY sh.start_time,s.name,ch.category,ch.name''',(date,office_id)).fetchall() if office_id else []
  groups={}
  for r in raw:
   key=r['staff_id']
   gd=groups.setdefault(key,{'batch_id':r['assignment_batch_id'] or f"legacy-{r['id']}",'legacy_id':r['id'] if not r['assignment_batch_id'] else None,'staff_id':r['staff_id'],'staff_name':r['staff_name'],'cs_name':r['cs_name'],'email':r['email'],'shift_id':r['shift_id'],'shift_name':r['shift_name'],'shift_code':r['shift_code'],'start_time':r['start_time'],'end_time':r['end_time'],'channel_ids':[],'channels':[]})
   gd['channel_ids'].append(r['channel_id']); gd['channels'].append({'id':r['channel_id'],'name':r['channel_name'] or r['target'] or 'Belum ada jobdesk','category':r['channel_category'] or r['category'] or 'Lainnya'})
  by_shift={}
  for sh in shifts:
   if sh['status']=='Aktif': by_shift[sh['id']]={'shift':sh,'staff':[]}
  for gd in groups.values():
   shift_obj=c.execute('SELECT * FROM shifts WHERE id=?',(gd['shift_id'],)).fetchone()
   by_shift.setdefault(gd['shift_id'],{'shift':shift_obj,'staff':[]})['staff'].append(gd)
  assigned_ids=set(groups.keys()); unassigned=[x for x in staff if x['id'] not in assigned_ids]
  # Bentrok hanya ditandai sebagai warning karena beberapa jobdesk dapat sengaja dipegang bersama.
  conflict_map={}
  for r in raw:
   if r['channel_id']:
    conflict_map.setdefault((r['shift_id'],r['channel_id'],r['channel_name'] or r['target']),set()).add(r['staff_name'])
  conflicts=[{'shift_id':k[0],'jobdesk':k[2],'staff':sorted(v)} for k,v in conflict_map.items() if len(v)>1]
  edit_staff=request.args.get('edit_staff',type=int); edit_row=groups.get(edit_staff)
  try: previous_date=(datetime.fromisoformat(date).date()-timedelta(days=1)).isoformat()
  except Exception: previous_date=(now().date()-timedelta(days=1)).isoformat()
 return render_template('operations.html',date=date,office_id=office_id,offices=offices,shifts=shifts,staff=staff,channels=channels,by_shift=list(by_shift.values()),unassigned=unassigned,edit_row=edit_row,conflicts=conflicts,previous_date=previous_date)

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
       c.execute('INSERT INTO leaves(staff_id,reason,out_at,expected_at,status,source,assignment_snapshot) VALUES(?,?,?,?,?,?,?)',(sid,reason,out.isoformat(),exp.isoformat(),'OUT','dashboard',snap)); c.commit()
       tg_send(INOUT_CHAT_ID,f"🚪 <b>IZIN KELUAR</b>\n👤 {staff['name']} — {staff['cs_name'] or '-'}\n💼 {jobdesk_text}\n📝 {reason.title()}\n⏳ Estimasi kembali: {exp.strftime('%H:%M')} WIB")
     except Exception:
      c.rollback(); raise
   elif action=='in':
    active_now=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
    if not active_now:
     flash('Tidak ada izin aktif untuk akun ini.','danger')
    else:
     t=now(); exp=datetime.fromisoformat(active_now['expected_at']); late=max(0,int((t-exp).total_seconds()//60)); fine=late*50000 if 1<=late<=9 else (500000 if late>=10 else 0)
     c.execute("UPDATE leaves SET in_at=?,status='IN',late_minutes=?,fine=? WHERE id=?",(t.isoformat(),late,fine,active_now['id'])); c.commit(); tg_send(INOUT_CHAT_ID,f"✅ <b>SUDAH KEMBALI</b>\n👤 {staff['name']}\n⏱ Terlambat: {late} menit\n💸 Denda: Rp{fine:,}")
   return redirect(url_for('inout_page'))
  active=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
  active_count=c.execute("SELECT COUNT(*) n FROM leaves WHERE status='OUT'").fetchone()['n']
  history=c.execute('SELECT * FROM leaves WHERE staff_id=? ORDER BY id DESC LIMIT 50',(sid,)).fetchall()
 return render_template('inout.html',staff=staff,active=active,history=history,assignment=ass,assignments=ass_rows,jobdesk_text=jobdesk_text,durations=DURATIONS,active_count=active_count,max_active=MAX_ACTIVE_LEAVES)

@app.get('/api/inout/active')
@login_required
def api_inout_active():
 with db_conn() as c:
  rows=c.execute("""SELECT l.id,l.staff_id,l.reason,l.out_at,l.expected_at,s.name,s.cs_name,o.name office_name
                    FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id
                    WHERE l.status='OUT' ORDER BY l.out_at ASC""").fetchall()
 data=[]
 for r in rows:
  data.append({'id':r['id'],'staff_id':r['staff_id'],'name':r['name'],'cs_name':r['cs_name'] or '-', 'office_name':r['office_name'] or '-', 'reason':r['reason'], 'out_at':r['out_at'], 'expected_at':r['expected_at']})
 return jsonify({'ok':True,'count':len(data),'max':MAX_ACTIVE_LEAVES,'is_full':len(data)>=MAX_ACTIVE_LEAVES,'items':data,'server_time':now().isoformat()})

@app.route('/warnings',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def warnings_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; wid=f.get('id',type=int); vals=(f.get('staff_id',type=int),f['type'],f['warning_date'],f['reason'].strip(),f.get('fine',type=int) or 0,f.get('notes','').strip())
   if wid:
    c.execute('UPDATE warnings SET staff_id=?,type=?,warning_date=?,reason=?,fine=?,notes=? WHERE id=?',vals+(wid,)); audit(c,'warning.update',f'id={wid}')
   else:
    c.execute('INSERT INTO warnings(staff_id,type,warning_date,reason,fine,notes,created_by,created_at) VALUES(?,?,?,?,?,?,?,?)',vals+(g.user['id'],now().isoformat())); audit(c,'warning.create',f'staff={vals[0]}')
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
  if request.method=='POST':c.execute("UPDATE staff SET status='Ex Karyawan',exit_date=?,exit_reason=? WHERE id=?",(request.form['exit_date'],request.form['exit_reason'],request.form['staff_id']));c.execute('UPDATE users SET is_active=0 WHERE staff_id=?',(request.form['staff_id'],));c.commit();return redirect(url_for('former_page'))
  rows=c.execute("SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE s.status='Ex Karyawan' ORDER BY s.name").fetchall(); active=c.execute("SELECT * FROM staff WHERE status='Aktif'").fetchall()
 return render_template('former.html',rows=rows,active=active)

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

# Deposit Monitor Sync PRO compatible API

def authorized(): return bool(API_KEY) and request.headers.get('X-API-Key','')==API_KEY
@app.get('/api/health')
def api_health(): return jsonify(status='ok',service='omtogel-staff-integrated',db=DB_PATH,lateMinutes=LATE_MINUTES,scanSeconds=SCAN_SECONDS)
@app.route('/api/heartbeat',methods=['POST'])
def heartbeat():
 if not authorized():return jsonify(error='API key tidak valid'),401
 d=request.get_json(silent=True) or {}; did=str(d.get('deviceId','')).strip(); name=str(d.get('deviceName') or 'Perangkat').strip()
 if not did:return jsonify(error='deviceId wajib'),400
 office_id=d.get('officeId')
 with db_conn() as c:
  existing=c.execute('SELECT device_id FROM devices WHERE device_id=?',(did,)).fetchone()
  if existing: c.execute('UPDATE devices SET device_name=?,office_id=COALESCE(?,office_id),last_seen=?,page_url=?,form_count=?,late_count=? WHERE device_id=?',(name,office_id,int(time.time()),d.get('pageUrl',''),int(d.get('formCount',0)),int(d.get('lateCount',0)),did))
  else: c.execute('INSERT INTO devices(device_id,device_name,office_id,last_seen,page_url,form_count,late_count) VALUES(?,?,?,?,?,?,?)',(did,name,office_id,int(time.time()),d.get('pageUrl',''),int(d.get('formCount',0)),int(d.get('lateCount',0))))
  c.commit(); leader=c.execute('SELECT device_id FROM devices WHERE last_seen>=? ORDER BY device_id LIMIT 1',(int(time.time())-LEADER_TTL_SECONDS,)).fetchone()
 return jsonify(ok=True,leaderDeviceId=leader['device_id'] if leader else did,settings={'enabled':True,'lateMinutes':LATE_MINUTES,'scanSeconds':SCAN_SECONDS})
@app.route('/api/forms',methods=['POST'])
@app.route('/api/form-alert',methods=['POST'])
def form_alert():
 if not authorized():return jsonify(error='API key tidak valid'),401
 d=request.get_json(silent=True) or {}; form_id=str(d.get('formId') or d.get('id') or '').strip(); device_id=str(d.get('deviceId') or '').strip(); destination=str(d.get('destination') or d.get('bank') or d.get('target') or '').strip()
 if not form_id:return jsonify(error='formId wajib'),400
 with db_conn() as c:
  dev=c.execute('SELECT * FROM devices WHERE device_id=?',(device_id,)).fetchone(); office_id=d.get('officeId') or (dev['office_id'] if dev else None)
  first=int(d.get('firstSeen') or time.time()); last=int(time.time()); status=d.get('status','pending'); age=int(d.get('ageMinutes') or max(0,(last-first)//60)); ass=find_assignment(c,office_id,destination,now()) if office_id else None; sid=ass['staff_id'] if ass else None
  leave=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone() if sid else None; staff_status='OUT' if leave else 'Aktif'
  existing_form=c.execute('SELECT id,staff_id,assignment_id FROM deposit_forms WHERE form_id=? ORDER BY id LIMIT 1',(form_id,)).fetchone(); processed_at=now().isoformat() if status in ('done','processed','completed') else None
  if existing_form:
   c.execute('UPDATE deposit_forms SET device_id=?,office_id=?,username=?,game_id=?,destination=?,destination_account=?,destination_owner=?,form_time=?,amount=?,bank=?,last_seen=?,status=?,staff_id=COALESCE(staff_id,?),assignment_id=COALESCE(assignment_id,?),staff_status=?,processed_at=? WHERE id=?',(device_id,office_id,d.get('username'),d.get('gameId'),destination,d.get('destinationAccount'),d.get('destinationOwner'),d.get('formTime'),str(d.get('amount','')),d.get('bank'),last,status,sid,ass['id'] if ass else None,staff_status,processed_at,existing_form['id']))
  else:
   c.execute('INSERT INTO deposit_forms(form_id,device_id,office_id,username,game_id,destination,destination_account,destination_owner,form_time,amount,bank,first_seen,last_seen,status,staff_id,assignment_id,staff_status,processed_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)',(form_id,device_id,office_id,d.get('username'),d.get('gameId'),destination,d.get('destinationAccount'),d.get('destinationOwner'),d.get('formTime'),str(d.get('amount','')),d.get('bank'),first,last,status,sid,ass['id'] if ass else None,staff_status,processed_at))
  row=c.execute('SELECT * FROM deposit_forms WHERE form_id=?',(form_id,)).fetchone(); should_alert=(status not in ('done','processed','completed') and age>=LATE_MINUTES and not row['alert_sent'])
  if should_alert:
   c.execute('UPDATE deposit_forms SET alert_sent=1 WHERE form_id=?',(form_id,)); staff=c.execute('SELECT s.*,o.name office_name,o.location FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE s.id=?',(sid,)).fetchone() if sid else None
   txt=f"⚠️ <b>FORM DEPOSIT TERLAMBAT</b>\n🏢 Kantor: {(staff['office_name'] if staff else '-') }\n👤 Staf: {(staff['name'] if staff else 'Belum terpetakan')}\n🎧 Nama CS: {(staff['cs_name'] if staff else '-')}\n💼 Jobdesk: {destination or '-'}\n🆔 Form: {form_id}\n💰 Nominal: {d.get('amount','-')}\n⏳ Umur form: {age} menit\n🟠 Status staf: {staff_status}"
   tg_send(ALERT_CHAT_ID,txt)
  c.commit()
 return jsonify(ok=True,formId=form_id,ageMinutes=age,alerted=should_alert,staffId=sid,staffName=ass['staff_name'] if ass else None,csName=ass['cs_name'] if ass else None,jobdesk=destination)
@app.get('/api/status')
def api_status():
 if not authorized():return jsonify(error='API key tidak valid'),401
 with db_conn() as c: devices=c.execute('SELECT * FROM devices ORDER BY last_seen DESC').fetchall()
 return jsonify(ok=True,devices=[dict(x) for x in devices],lateMinutes=LATE_MINUTES,scanSeconds=SCAN_SECONDS)



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
  pending=c.execute('''SELECT s.id,s.name,s.cs_name,o.name office_name,COUNT(f.id) pending_count,MAX(CAST((f.last_seen-f.first_seen)/60 AS INTEGER)) max_age,ROUND(AVG(CAST((f.last_seen-f.first_seen)/60.0 AS REAL)),1) avg_age
    FROM deposit_forms f JOIN staff s ON s.id=f.staff_id LEFT JOIN offices o ON o.id=s.office_id
    WHERE f.alert_sent=1 AND f.first_seen>=? AND f.first_seen<?'''+extra_where+''' GROUP BY s.id ORDER BY pending_count DESC,max_age DESC,s.name''',p).fetchall()
  lp=[start_dt.isoformat(),end_dt.isoformat()]; lclauses=[]
  if office_id:lclauses.append('s.office_id=?');lp.append(office_id)
  if staff_id:lclauses.append('s.id=?');lp.append(staff_id)
  lw=(' AND '+' AND '.join(lclauses)) if lclauses else ''
  inout=c.execute('''SELECT s.id,s.name,s.cs_name,o.name office_name,COUNT(l.id) total_out,SUM(CASE WHEN l.late_minutes>0 THEN 1 ELSE 0 END) late_count,SUM(l.late_minutes) late_minutes,SUM(l.fine) total_fine,SUM(CASE WHEN l.status='OUT' THEN 1 ELSE 0 END) not_in_count
    FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.out_at>=? AND l.out_at<=?'''+lw+''' GROUP BY s.id ORDER BY late_count DESC,not_in_count DESC,total_out DESC''',lp).fetchall()
  totals={'pending':sum((x['pending_count'] or 0) for x in pending),'out':sum((x['total_out'] or 0) for x in inout),'late':sum((x['late_count'] or 0) for x in inout),'fine':sum((x['total_fine'] or 0) for x in inout)}
 return render_template('leader_reports.html',pending=pending,inout=inout,totals=totals,offices=offices,staff=staff,start=start,end=end,office_id=office_id,staff_id=staff_id,retention_days=RETENTION_DAYS)

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
 sid=g.user['staff_id']
 if not sid:return ('Akun tidak terhubung ke staf.',400)
 with db_conn() as c:
  if request.method=='POST':
   mid=request.form.get('id',type=int); note=(request.form.get('staff_note') or '').strip(); row=c.execute('SELECT * FROM mistake_ledger WHERE id=? AND staff_id=?',(mid,sid)).fetchone()
   if row:c.execute('UPDATE mistake_ledger SET staff_note=?,updated_at=? WHERE id=?',(note,now().isoformat(),mid));c.commit();flash('Catatan pribadi berhasil disimpan.','success')
   return redirect(url_for('mistakes_page'))
  rows=c.execute('SELECT * FROM mistake_ledger WHERE staff_id=? ORDER BY entry_date DESC,id DESC',(sid,)).fetchall()
  total_mistake=sum(r['amount'] for r in rows if r['entry_type']=='MISTAKE'); total_cut=sum(r['amount'] for r in rows if r['entry_type']=='POTONGAN'); remaining=max(0,total_mistake-total_cut)
 return render_template('mistakes.html',rows=rows,total_mistake=total_mistake,total_cut=total_cut,remaining=remaining)

@app.route('/mistakes/manage',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def mistakes_manage_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; mid=f.get('id',type=int); vals=(f.get('staff_id',type=int),f.get('entry_date') or now().date().isoformat(),f.get('entry_type'),f.get('amount',type=int) or 0,(f.get('title') or '').strip(),(f.get('notes') or '').strip())
   if mid:c.execute('UPDATE mistake_ledger SET staff_id=?,entry_date=?,entry_type=?,amount=?,title=?,notes=?,updated_at=? WHERE id=?',vals+(now().isoformat(),mid));audit(c,'mistake.update',f'id={mid}')
   else:c.execute('INSERT INTO mistake_ledger(staff_id,entry_date,entry_type,amount,title,notes,created_by,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?)',vals+(g.user['id'],now().isoformat(),now().isoformat()));audit(c,'mistake.create',f'staff={vals[0]} amount={vals[3]}')
   c.commit();flash('Catatan mistake berhasil disimpan.','success');return redirect(url_for('mistakes_manage_page'))
  rows=c.execute('SELECT m.*,s.name staff_name,o.name office_name FROM mistake_ledger m JOIN staff s ON s.id=m.staff_id LEFT JOIN offices o ON o.id=s.office_id ORDER BY m.entry_date DESC,m.id DESC LIMIT 500').fetchall(); staff=c.execute("SELECT id,name FROM staff WHERE status='Aktif' ORDER BY name").fetchall()
 return render_template('mistakes_manage.html',rows=rows,staff=staff)

@app.post('/mistakes/manage/<int:mid>/delete')
@roles('superadmin','supervisor')
def mistake_delete(mid):
 with db_conn() as c:
  old=c.execute('SELECT * FROM mistake_ledger WHERE id=?',(mid,)).fetchone()
  if old:audit(c,'mistake.delete',json.dumps(dict(old),default=str));c.execute('DELETE FROM mistake_ledger WHERE id=?',(mid,));c.commit()
 flash('Catatan mistake dihapus.','success');return redirect(url_for('mistakes_manage_page'))

@app.get('/history')
@login_required
def my_history_page():
 if g.user['role']=='staff' and not menu_allowed('history'): return ('Akses History Saya dinonaktifkan oleh Master.',403)
 sid=g.user['staff_id']
 if not sid:return ('Akun tidak terhubung ke staf.',400)
 cutoff=now()-timedelta(days=RETENTION_DAYS); start_ts=int(cutoff.timestamp())
 with db_conn() as c:
  sp=c.execute('SELECT * FROM warnings WHERE staff_id=? ORDER BY warning_date DESC,id DESC',(sid,)).fetchall(); leaves=c.execute('SELECT * FROM leaves WHERE staff_id=? AND out_at>=? ORDER BY out_at DESC',(sid,cutoff.isoformat())).fetchall(); pending=c.execute('SELECT * FROM deposit_forms WHERE staff_id=? AND alert_sent=1 AND first_seen>=? ORDER BY first_seen DESC',(sid,start_ts)).fetchall(); mistakes=c.execute('SELECT * FROM mistake_ledger WHERE staff_id=? ORDER BY entry_date DESC,id DESC',(sid,)).fetchall()
  summary={'sp':len(sp),'pending':len(pending),'late_inout':sum(1 for x in leaves if (x['late_minutes'] or 0)>0),'fine':sum((x['fine'] or 0) for x in leaves),'mistake':sum(x['amount'] for x in mistakes if x['entry_type']=='MISTAKE'),'cut':sum(x['amount'] for x in mistakes if x['entry_type']=='POTONGAN')}
 return render_template('history.html',sp=sp,leaves=leaves,pending=pending,mistakes=mistakes,summary=summary,retention_days=RETENTION_DAYS)

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
    for l in c.execute("SELECT l.*,s.name,s.cs_name FROM leaves l JOIN staff s ON s.id=l.staff_id WHERE l.status='OUT' AND l.notified_overdue=0").fetchall():
     if now()>datetime.fromisoformat(l['expected_at']):
      c.execute('UPDATE leaves SET notified_overdue=1 WHERE id=?',(l['id'],)); tg_send(INOUT_CHAT_ID,f"🔴 <b>MELEWATI ESTIMASI</b>\n👤 {l['name']} — {l['cs_name'] or '-'}\n📝 {l['reason'].title()}")
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
  time.sleep(30)
def start_bg():
 global bg_started
 if not bg_started:bg_started=True;threading.Thread(target=background,daemon=True).start()

init_db();start_bg();print('[startup] SQLite database:',DB_PATH,flush=True)
if __name__=='__main__':app.run(host='0.0.0.0',port=int(os.getenv('PORT','8080')))
