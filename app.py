import os, json, time, sqlite3, threading, secrets, re, uuid
from datetime import datetime, timedelta
from functools import wraps
from zoneinfo import ZoneInfo
import requests, base64, hmac, hashlib, struct
from flask import Flask, render_template, request, redirect, url_for, session, flash, jsonify, g
from werkzeug.security import generate_password_hash, check_password_hash

WIB=ZoneInfo('Asia/Jakarta')
DURATIONS={'makan':20,'merokok':10,'toilet':5,'bab':15}
MAX_ACTIVE_LEAVES=int(os.getenv('MAX_ACTIVE_LEAVES','5'))
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
    CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY AUTOINCREMENT,username TEXT UNIQUE NOT NULL,password_hash TEXT NOT NULL,role TEXT DEFAULT 'staff',staff_id INTEGER UNIQUE,office_id INTEGER,is_active INTEGER DEFAULT 1,must_change_password INTEGER DEFAULT 1,allowed_menus TEXT DEFAULT '["my_dashboard","inout","memo","account"]',device_token TEXT,last_login TEXT,twofa_secret TEXT,twofa_enabled INTEGER DEFAULT 0,FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(office_id) REFERENCES offices(id));
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
      'staff': [('telegram_id','TEXT'),('telegram_username','TEXT'),('email','TEXT'),('agent_code','TEXT'),('cs_name','TEXT'),('office_id','INTEGER'),('position',"TEXT DEFAULT 'CS'"),('status',"TEXT DEFAULT 'Aktif'"),('join_date','TEXT'),('exit_date','TEXT'),('exit_reason','TEXT'),('notes','TEXT')],
      'users': [('role',"TEXT DEFAULT 'staff'"),('staff_id','INTEGER'),('office_id','INTEGER'),('is_active','INTEGER DEFAULT 1'),('must_change_password','INTEGER DEFAULT 1'),('allowed_menus',"TEXT DEFAULT '[\"my_dashboard\",\"inout\",\"memo\",\"account\"]'"),('device_token','TEXT'),('last_login','TEXT'),('twofa_secret','TEXT'),('twofa_enabled','INTEGER DEFAULT 0')],
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
    c.execute("INSERT OR IGNORE INTO offices(name,location) VALUES('Kantor Utama','-')"); oid=c.execute('SELECT id FROM offices ORDER BY id LIMIT 1').fetchone()[0]
    c.execute("INSERT OR IGNORE INTO shifts(office_id,name,code,start_time,end_time) VALUES(?,?,?,?,?)",(oid,'Pagi','P1','06:00','18:00'))
    c.execute("INSERT OR IGNORE INTO shifts(office_id,name,code,start_time,end_time) VALUES(?,?,?,?,?)",(oid,'Malam','M1','18:00','06:00'))
    for k,v in {'late_minutes':str(LATE_MINUTES),'scan_seconds':str(SCAN_SECONDS)}.items(): c.execute('INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)',(k,v))
    if not c.execute('SELECT 1 FROM users WHERE username=?',(ADMIN_USERNAME,)).fetchone():
      c.execute('INSERT INTO users(username,password_hash,role,office_id,is_active,must_change_password,allowed_menus) VALUES(?,?,?,?,1,0,?)',(ADMIN_USERNAME,generate_password_hash(ADMIN_PASSWORD),'superadmin',oid,json.dumps(['*'])))
    c.commit()

def audit(c,action,detail=''): c.execute('INSERT INTO audit_logs(user_id,action,detail,created_at) VALUES(?,?,?,?)',(g.user['id'] if getattr(g,'user',None) else None,action,detail,now().isoformat()))
def tg_send(chat_id,text):
  if not BOT_TOKEN or not chat_id:return False
  try:return requests.post(f'https://api.telegram.org/bot{BOT_TOKEN}/sendMessage',json={'chat_id':chat_id,'text':text,'parse_mode':'HTML'},timeout=15).ok
  except Exception:return False

@app.before_request
def before():
 g.user=None; g.policy_pending=False
 if session.get('uid'):
  with db_conn() as c:
   g.user=c.execute('SELECT * FROM users WHERE id=? AND is_active=1',(session['uid'],)).fetchone()
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

def active_shift(c,office_id,when=None):
 when=when or now(); hm=when.strftime('%H:%M')
 for s in c.execute("SELECT * FROM shifts WHERE office_id=? AND status='Aktif'",(office_id,)):
  st=s['start_time']; en=s['end_time']; ok=(st<=hm<en) if st<en else (hm>=st or hm<en)
  if ok:return s
 return None


def staff_active_assignments(c,staff_id,when=None):
 when=when or now(); date=when.date().isoformat(); hm=when.strftime('%H:%M')
 rows=c.execute("""SELECT a.*,ch.name channel_name FROM assignments a LEFT JOIN channels ch ON ch.id=a.channel_id WHERE a.staff_id=? AND a.work_date=? AND a.is_active=1 ORDER BY ch.category,ch.name""",(staff_id,date)).fetchall()
 active=[]
 for r in rows:
  st=r['start_time'] or '00:00'; en=r['end_time'] or '23:59'; ok=(st<=hm<en) if st<en else (hm>=st or hm<en)
  if ok: active.append(r)
 return active

def find_assignment(c,office_id,target,when=None):
 when=when or now(); date=when.date().isoformat(); hm=when.strftime('%H:%M'); target_norm=re.sub(r'[^a-z0-9]','',target.lower())
 rows=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,s.telegram_id,s.agent_code,o.name office_name,o.location,sh.name shift_name,ch.name channel_name,ch.aliases
 FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id
 WHERE a.office_id=? AND a.work_date=? AND a.is_active=1 AND s.status='Aktif' ''',(office_id,date)).fetchall()
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
   session['uid']=u['id']; session['policy_pending']=True; c.execute('UPDATE users SET last_login=? WHERE id=?',(now().isoformat(),u['id'])); c.commit(); return redirect(url_for('dashboard'))
 return render_template('login.html')
@app.route('/2fa/verify',methods=['GET','POST'])
def twofa_verify():
 uid=session.get('pending_uid')
 if not uid:return redirect(url_for('login'))
 with db_conn() as c:u=c.execute('SELECT * FROM users WHERE id=?',(uid,)).fetchone()
 if request.method=='POST':
  if totp_verify(u['twofa_secret'],request.form['code'].strip()): session.pop('pending_uid',None); session['uid']=uid; session['policy_pending']=True; return redirect(url_for('dashboard'))
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
def logout():session.clear();return redirect(url_for('login'))

@app.get('/')
@login_required
def dashboard():
 with db_conn() as c:
  today=now().date().isoformat(); office_id=request.args.get('office_id',type=int) or g.user['office_id']
  offices=c.execute("SELECT * FROM offices WHERE status='Aktif'").fetchall(); params=[]; where=' WHERE 1=1 '
  if office_id:where+=' AND s.office_id=?';params.append(office_id)
  staff=c.execute('SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id'+where+' ORDER BY s.name',params).fetchall()
  assignments=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,o.name office_name,sh.name shift_name,ch.name channel_name,ch.category category FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id WHERE a.work_date=?'''+(' AND a.office_id=?' if office_id else '')+' ORDER BY o.name,sh.start_time,ch.category,ch.name',(today,office_id) if office_id else (today,)).fetchall()
  leaves=c.execute("SELECT l.*,s.name,s.cs_name,o.name office_name FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.status='OUT'"+(' AND s.office_id=?' if office_id else ''),(office_id,) if office_id else ()).fetchall()
  alerts=c.execute('''SELECT d.*,s.name staff_name,s.cs_name,o.name office_name FROM deposit_forms d LEFT JOIN staff s ON s.id=d.staff_id LEFT JOIN offices o ON o.id=d.office_id WHERE d.alert_sent=1'''+(' AND d.office_id=?' if office_id else '')+' ORDER BY d.id DESC LIMIT 50',(office_id,) if office_id else ()).fetchall()
  stats={'staff':sum(1 for x in staff if x['status']=='Aktif'),'out':len(leaves),'alerts':len(alerts),'ex':sum(1 for x in staff if x['status']=='Ex Karyawan')}
 boards={}
 for r in assignments:
  key=f"{r['category'] or 'LAINNYA'}|{r['shift_name'] or '-'}"
  boards.setdefault(key,{'title':f"{(r['category'] or 'LAINNYA').upper()} {str(r['shift_name'] or '').upper()}",'items':[]})['items'].append(r)
 return render_template('dashboard.html',offices=offices,office_id=office_id,staff=staff,assignments=assignments,boards=list(boards.values()),leaves=leaves,alerts=alerts,stats=stats)

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
  used=any(c.execute(q,(oid,)).fetchone() for q in ['SELECT 1 FROM staff WHERE office_id=? LIMIT 1','SELECT 1 FROM assignments WHERE office_id=? LIMIT 1','SELECT 1 FROM shifts WHERE office_id=? LIMIT 1'])
  if used: c.execute("UPDATE offices SET status='Nonaktif' WHERE id=?",(oid,)); flash('Kantor sudah memiliki data terkait, jadi dinonaktifkan.','success')
  else: c.execute('DELETE FROM offices WHERE id=?',(oid,)); flash('Kantor berhasil dihapus.','success')
  c.commit()
 return redirect(url_for('offices_page'))

@app.route('/shifts',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def shifts_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; sid=f.get('id',type=int); vals=(f.get('office_id',type=int),f['name'].strip(),f.get('code','').strip(),f['start_time'],f['end_time'],f.get('status','Aktif'))
   try:
    if sid:
     c.execute('UPDATE shifts SET office_id=?,name=?,code=?,start_time=?,end_time=?,status=? WHERE id=?',vals+(sid,)); audit(c,'shift.update',str(sid))
    else:
     c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(?,?,?,?,?,?)',vals); audit(c,'shift.create',f['name'])
    c.commit(); flash('Shift berhasil disimpan.','success')
   except sqlite3.IntegrityError:
    c.rollback(); flash('Nama shift sudah ada pada kantor tersebut.','danger')
   return redirect(url_for('shifts_page'))
  rows=c.execute('SELECT sh.*,o.name office_name FROM shifts sh JOIN offices o ON o.id=sh.office_id ORDER BY o.name,sh.start_time').fetchall(); offices=c.execute('SELECT * FROM offices ORDER BY name').fetchall()
 return render_template('shifts.html',rows=rows,offices=offices)

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
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; cid=f.get('id',type=int); vals=(f.get('office_id',type=int),f['name'].strip(),f['category'],f.get('aliases','').strip(),f.get('status','Aktif'))
   if cid: c.execute('UPDATE channels SET office_id=?,name=?,category=?,aliases=?,status=? WHERE id=?',vals+(cid,)); audit(c,'channel.update',f'id={cid}')
   else: c.execute('INSERT INTO channels(office_id,name,category,aliases,status) VALUES(?,?,?,?,?)',vals); audit(c,'channel.create',vals[1])
   c.commit(); flash('Bank / channel berhasil disimpan.','success'); return redirect(url_for('channels_page'))
  rows=c.execute('SELECT ch.*,o.name office_name FROM channels ch JOIN offices o ON o.id=ch.office_id ORDER BY o.name,ch.category,ch.name').fetchall(); offices=c.execute('SELECT * FROM offices ORDER BY name').fetchall()
 return render_template('channels.html',rows=rows,offices=offices)

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
   f=request.form; sid=f.get('id',type=int); vals=(f['name'].strip(),f.get('telegram_id') or None,f.get('telegram_username',''),f.get('email',''),f.get('agent_code',''),f.get('cs_name',''),f.get('office_id',type=int),f.get('position','CS'),f.get('status','Aktif'),f.get('join_date') or None,f.get('notes',''))
   if sid:c.execute('UPDATE staff SET name=?,telegram_id=?,telegram_username=?,email=?,agent_code=?,cs_name=?,office_id=?,position=?,status=?,join_date=?,notes=? WHERE id=?',vals+(sid,))
   else:sid=c.execute('INSERT INTO staff(name,telegram_id,telegram_username,email,agent_code,cs_name,office_id,position,status,join_date,notes) VALUES(?,?,?,?,?,?,?,?,?,?,?)',vals).lastrowid
   if f.get('login_id'):
    login_id=f['login_id'].strip(); existing_user=c.execute('SELECT id FROM users WHERE staff_id=?',(sid,)).fetchone(); username_owner=c.execute('SELECT id,staff_id FROM users WHERE username=?',(login_id,)).fetchone()
    if username_owner and (not existing_user or username_owner['id']!=existing_user['id']):
     c.rollback(); flash('ID login sudah dipakai akun lain.','danger'); return redirect(url_for('staff_page'))
    if existing_user:
     if f.get('password'): c.execute('UPDATE users SET username=?,password_hash=?,office_id=?,is_active=1,must_change_password=1 WHERE id=?',(login_id,generate_password_hash(f['password']),f.get('office_id',type=int),existing_user['id']))
     else: c.execute('UPDATE users SET username=?,office_id=?,is_active=1 WHERE id=?',(login_id,f.get('office_id',type=int),existing_user['id']))
    else:
     pw=f.get('password') or secrets.token_urlsafe(6); c.execute('INSERT INTO users(username,password_hash,role,staff_id,office_id,is_active,must_change_password) VALUES(?,?,?,?,?,1,1)',(login_id,generate_password_hash(pw),'staff',sid,f.get('office_id',type=int)))
   c.commit(); flash('Data staf tersimpan.','success'); return redirect(url_for('staff_page'))
  rows=c.execute('SELECT s.*,o.name office_name,u.username login_id,u.is_active account_active FROM staff s LEFT JOIN offices o ON o.id=s.office_id LEFT JOIN users u ON u.staff_id=s.id ORDER BY s.status,s.name').fetchall(); offices=c.execute('SELECT * FROM offices').fetchall()
 return render_template('staff.html',rows=rows,offices=offices)

@app.post('/staff/<int:sid>/reset-password')
@roles('superadmin','supervisor','leader')
def reset_password(sid):
 pw=request.form.get('password') or secrets.token_urlsafe(7)
 with db_conn() as c:c.execute('UPDATE users SET password_hash=?,must_change_password=1 WHERE staff_id=?',(generate_password_hash(pw),sid));c.commit()
 flash('Password direset. Password baru: '+pw,'success');return redirect(url_for('staff_page'))

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

@app.route('/assignments',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def assignments_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; action=f.get('action','save'); batch_id=(f.get('batch_id') or '').strip(); legacy_id=f.get('legacy_id',type=int)
   if action=='delete':
    if batch_id and not batch_id.startswith('legacy-'): c.execute('DELETE FROM assignments WHERE assignment_batch_id=?',(batch_id,))
    elif legacy_id: c.execute('DELETE FROM assignments WHERE id=?',(legacy_id,))
    c.commit(); flash('Jobdesk berhasil dihapus.','success'); return redirect(url_for('assignments_page',date=f.get('work_date')))
   channel_ids=[]
   for raw in f.getlist('channel_ids'):
    try:
     cid=int(raw)
     if cid not in channel_ids: channel_ids.append(cid)
    except (TypeError,ValueError): pass
   if not 1 <= len(channel_ids) <= 10:
    flash('Pilih minimal 1 dan maksimal 10 jobdesk.','danger'); return redirect(url_for('assignments_page',date=f.get('work_date')))
   sh=c.execute('SELECT * FROM shifts WHERE id=? AND status=?',(f.get('shift_id',type=int),'Aktif')).fetchone(); st=c.execute('SELECT * FROM staff WHERE id=? AND status=?',(f.get('staff_id',type=int),'Aktif')).fetchone()
   if not sh or not st:
    flash('Shift atau staf tidak valid.','danger'); return redirect(url_for('assignments_page',date=f.get('work_date')))
   if not batch_id or batch_id.startswith('legacy-'): batch_id=uuid.uuid4().hex
   else: c.execute('DELETE FROM assignments WHERE assignment_batch_id=?',(batch_id,))
   for cid in channel_ids:
    ch=c.execute('SELECT * FROM channels WHERE id=? AND status=?',(cid,'Aktif')).fetchone()
    if not ch: continue
    c.execute('INSERT INTO assignments(assignment_batch_id,work_date,office_id,shift_id,staff_id,channel_id,category,target,start_time,end_time,is_active) VALUES(?,?,?,?,?,?,?,?,?,?,1)',(batch_id,f['work_date'],f.get('office_id',type=int),f.get('shift_id',type=int),f.get('staff_id',type=int),cid,ch['category'],ch['name'],f.get('start_time') or sh['start_time'],f.get('end_time') or sh['end_time']))
   audit(c,'assignment.save',f"{f['work_date']} staff={f.get('staff_id')} channels={channel_ids}"); c.commit(); flash('Jobdesk harian berhasil disimpan.','success'); return redirect(url_for('assignments_page',date=f['work_date']))
  date=request.args.get('date') or now().date().isoformat(); edit_key=request.args.get('edit')
  raw=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,o.name office_name,sh.name shift_name,ch.name channel_name,ch.category channel_category FROM assignments a JOIN staff s ON s.id=a.staff_id JOIN offices o ON o.id=a.office_id JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id WHERE a.work_date=? ORDER BY o.name,sh.start_time,s.name,ch.category,ch.name''',(date,)).fetchall()
  groups={}
  for r in raw:
   key=r['assignment_batch_id'] or f"legacy-{r['id']}"
   gd=groups.setdefault(key,{'batch_id':key,'legacy_id':r['id'] if not r['assignment_batch_id'] else None,'work_date':r['work_date'],'office_id':r['office_id'],'office_name':r['office_name'],'shift_id':r['shift_id'],'shift_name':r['shift_name'],'staff_id':r['staff_id'],'staff_name':r['staff_name'],'cs_name':r['cs_name'],'start_time':r['start_time'],'end_time':r['end_time'],'channels':[],'channel_ids':[]})
   gd['channels'].append(r['channel_name'] or r['target'] or 'Belum ada jobdesk'); gd['channel_ids'].append(r['channel_id'])
  rows=list(groups.values()); edit_row=groups.get(edit_key)
  offices=c.execute("SELECT * FROM offices WHERE status='Aktif' ORDER BY name").fetchall(); shifts=c.execute("SELECT * FROM shifts WHERE status='Aktif' ORDER BY office_id,start_time").fetchall(); staff=c.execute("SELECT * FROM staff WHERE status='Aktif' ORDER BY name").fetchall(); channels=c.execute("SELECT * FROM channels WHERE status='Aktif' ORDER BY category,name").fetchall()
 return render_template('assignments.html',date=date,rows=rows,offices=offices,shifts=shifts,staff=staff,channels=channels,edit_row=edit_row)

@app.route('/inout',methods=['GET','POST'])
@login_required
def inout_page():
 if not g.user['staff_id']: return ('Akun ini tidak terhubung ke Data Staf.',400)
 sid=g.user['staff_id']
 with db_conn() as c:
  staff=c.execute('SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE s.id=?',(sid,)).fetchone(); active=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone(); ass_rows=staff_active_assignments(c,sid,now()); ass=ass_rows[0] if ass_rows else None; jobdesk_text=', '.join((r['channel_name'] or r['target'] or '-') for r in ass_rows) or '-'
  if request.method=='POST':
   action=request.form['action']
   if action=='out':
    if active:flash('Kamu masih izin keluar.','danger')
    elif c.execute("SELECT COUNT(*) n FROM leaves WHERE status='OUT'").fetchone()['n']>=MAX_ACTIVE_LEAVES:flash(f'Maksimal {MAX_ACTIVE_LEAVES} orang izin bersamaan.','danger')
    else:
     reason=request.form['reason']; out=now(); exp=out+timedelta(minutes=DURATIONS[reason]); snap=json.dumps({'jobdesk':jobdesk_text,'cs':staff['cs_name'],'office':staff['office_name']})
     c.execute('INSERT INTO leaves(staff_id,reason,out_at,expected_at,status,source,assignment_snapshot) VALUES(?,?,?,?,?,?,?)',(sid,reason,out.isoformat(),exp.isoformat(),'OUT','dashboard',snap));c.commit();tg_send(INOUT_CHAT_ID,f"🚪 <b>IZIN KELUAR</b>\n👤 {staff['name']} — {staff['cs_name'] or '-'}\n💼 {jobdesk_text}\n📝 {reason.title()}\n⏳ Estimasi kembali: {exp.strftime('%H:%M')} WIB")
   elif action=='in' and active:
    t=now(); exp=datetime.fromisoformat(active['expected_at']); late=max(0,int((t-exp).total_seconds()//60)); fine=late*50000 if 1<=late<=9 else (500000 if late>=10 else 0); c.execute("UPDATE leaves SET in_at=?,status='IN',late_minutes=?,fine=? WHERE id=?",(t.isoformat(),late,fine,active['id']));c.commit();tg_send(INOUT_CHAT_ID,f"✅ <b>SUDAH KEMBALI</b>\n👤 {staff['name']}\n⏱ Terlambat: {late} menit\n💸 Denda: Rp{fine:,}")
   return redirect(url_for('inout_page'))
  history=c.execute('SELECT * FROM leaves WHERE staff_id=? ORDER BY id DESC LIMIT 50',(sid,)).fetchall()
 return render_template('inout.html',staff=staff,active=active,history=history,assignment=ass,assignments=ass_rows,jobdesk_text=jobdesk_text,durations=DURATIONS)

@app.route('/warnings',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def warnings_page():
 with db_conn() as c:
  if request.method=='POST':c.execute('INSERT INTO warnings(staff_id,type,warning_date,reason,fine,notes,created_by,created_at) VALUES(?,?,?,?,?,?,?,?)',(request.form['staff_id'],request.form['type'],request.form['warning_date'],request.form['reason'],request.form.get('fine',0),request.form.get('notes',''),g.user['id'],now().isoformat()));c.commit();return redirect(url_for('warnings_page'))
  rows=c.execute('SELECT w.*,s.name,s.cs_name,o.name office_name FROM warnings w JOIN staff s ON s.id=w.staff_id LEFT JOIN offices o ON o.id=s.office_id ORDER BY w.id DESC').fetchall(); staff=c.execute("SELECT * FROM staff WHERE status!='Ex Karyawan'").fetchall()
 return render_template('warnings.html',rows=rows,staff=staff)

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
 with db_conn() as c:
  if request.method=='POST' and g.user['staff_id']:
   c.execute('INSERT INTO memos(staff_id,title,category,body,priority,created_at,updated_at) VALUES(?,?,?,?,?,?,?)',(g.user['staff_id'],request.form['title'],request.form['category'],request.form['body'],request.form.get('priority','Normal'),now().isoformat(),now().isoformat()));c.commit();return redirect(url_for('memos_page'))
  if g.user['role']=='staff':rows=c.execute('SELECT m.*,s.name FROM memos m JOIN staff s ON s.id=m.staff_id WHERE m.staff_id=? ORDER BY m.id DESC',(g.user['staff_id'],)).fetchall()
  else:rows=c.execute('SELECT m.*,s.name,s.cs_name,o.name office_name FROM memos m JOIN staff s ON s.id=m.staff_id LEFT JOIN offices o ON o.id=s.office_id ORDER BY m.id DESC').fetchall()
 return render_template('memos.html',rows=rows)
@app.post('/memos/<int:mid>/reply')
@roles('superadmin','supervisor','leader')
def memo_reply(mid):
 with db_conn() as c:c.execute('UPDATE memos SET leader_reply=?,status=?,updated_at=? WHERE id=?',(request.form['reply'],request.form['status'],now().isoformat(),mid));c.commit()
 return redirect(url_for('memos_page'))

@app.get('/monitor')
@roles('superadmin','supervisor','leader')
def monitor_page():
 with db_conn() as c:devices=c.execute('SELECT d.*,o.name office_name FROM devices d LEFT JOIN offices o ON o.id=d.office_id ORDER BY d.last_seen DESC').fetchall();forms=c.execute('SELECT f.*,s.name staff_name,s.cs_name,o.name office_name FROM deposit_forms f LEFT JOIN staff s ON s.id=f.staff_id LEFT JOIN offices o ON o.id=f.office_id ORDER BY f.id DESC LIMIT 200').fetchall(); offices=c.execute('SELECT * FROM offices').fetchall()
 return render_template('monitor.html',devices=devices,forms=forms,offices=offices,now_ts=int(time.time()),ttl=LEADER_TTL_SECONDS)

@app.get('/reports')
@roles('superadmin','supervisor','leader')
def reports_page():
 with db_conn() as c:
  rows=c.execute('''SELECT s.id,s.name,s.cs_name,o.name office_name,COUNT(f.id) total_forms,SUM(CASE WHEN f.alert_sent=1 THEN 1 ELSE 0 END) late_forms,MAX(CASE WHEN f.first_seen>0 THEN CAST((COALESCE(strftime('%s',f.processed_at),f.last_seen)-f.first_seen)/60 AS INTEGER) ELSE 0 END) max_age FROM staff s LEFT JOIN offices o ON o.id=s.office_id LEFT JOIN deposit_forms f ON f.staff_id=s.id GROUP BY s.id ORDER BY late_forms DESC''').fetchall()
  leaves=c.execute('SELECT s.name,COUNT(l.id) total_out,SUM(l.late_minutes) late_minutes,SUM(l.fine) fine FROM staff s LEFT JOIN leaves l ON l.staff_id=s.id GROUP BY s.id ORDER BY fine DESC').fetchall()
 return render_template('reports.html',rows=rows,leaves=leaves)

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
 while True:
  try:
   with db_conn() as c:
    for l in c.execute("SELECT l.*,s.name,s.cs_name FROM leaves l JOIN staff s ON s.id=l.staff_id WHERE l.status='OUT' AND l.notified_overdue=0").fetchall():
     if now()>datetime.fromisoformat(l['expected_at']): c.execute('UPDATE leaves SET notified_overdue=1 WHERE id=?',(l['id'],));tg_send(INOUT_CHAT_ID,f"🔴 <b>MELEWATI ESTIMASI</b>\n👤 {l['name']} — {l['cs_name'] or '-'}\n📝 {l['reason'].title()}")
    c.commit()
  except Exception as e:print('[background]',e,flush=True)
  time.sleep(30)
def start_bg():
 global bg_started
 if not bg_started:bg_started=True;threading.Thread(target=background,daemon=True).start()

init_db();start_bg();print('[startup] SQLite database:',DB_PATH,flush=True)
if __name__=='__main__':app.run(host='0.0.0.0',port=int(os.getenv('PORT','8080')))
