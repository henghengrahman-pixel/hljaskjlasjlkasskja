import os, json, time, sqlite3, threading, secrets, re
from datetime import datetime, timedelta
from functools import wraps
from zoneinfo import ZoneInfo
import requests, base64, hmac, hashlib, struct
from flask import Flask, render_template, request, redirect, url_for, session, flash, jsonify, g
from werkzeug.security import generate_password_hash, check_password_hash

WIB=ZoneInfo('Asia/Jakarta')
DURATIONS={'makan':20,'merokok':10,'toilet':5,'bab':15}
MAX_ACTIVE_LEAVES=int(os.getenv('MAX_ACTIVE_LEAVES','5'))

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
    CREATE TABLE IF NOT EXISTS assignments(id INTEGER PRIMARY KEY AUTOINCREMENT,work_date TEXT NOT NULL,office_id INTEGER,shift_id INTEGER,staff_id INTEGER,channel_id INTEGER,category TEXT,target TEXT,start_time TEXT,end_time TEXT,is_active INTEGER DEFAULT 1,FOREIGN KEY(office_id) REFERENCES offices(id),FOREIGN KEY(shift_id) REFERENCES shifts(id),FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(channel_id) REFERENCES channels(id));
    CREATE TABLE IF NOT EXISTS offdays(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,off_date TEXT,notes TEXT,created_at TEXT,UNIQUE(staff_id,off_date),FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS leaves(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER NOT NULL,reason TEXT,out_at TEXT,expected_at TEXT,in_at TEXT,status TEXT DEFAULT 'OUT',late_minutes INTEGER DEFAULT 0,fine INTEGER DEFAULT 0,source TEXT,notified_overdue INTEGER DEFAULT 0,assignment_snapshot TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS warnings(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,type TEXT,warning_date TEXT,reason TEXT,fine INTEGER DEFAULT 0,notes TEXT,created_by INTEGER,created_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS memos(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,title TEXT,category TEXT,body TEXT,priority TEXT DEFAULT 'Normal',status TEXT DEFAULT 'Baru',leader_reply TEXT,created_at TEXT,updated_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS devices(device_id TEXT PRIMARY KEY,device_name TEXT,office_id INTEGER,last_seen INTEGER,page_url TEXT,form_count INTEGER DEFAULT 0,late_count INTEGER DEFAULT 0,FOREIGN KEY(office_id) REFERENCES offices(id));
    CREATE TABLE IF NOT EXISTS deposit_forms(id INTEGER PRIMARY KEY AUTOINCREMENT,form_id TEXT UNIQUE,device_id TEXT,office_id INTEGER,username TEXT,game_id TEXT,destination TEXT,destination_account TEXT,destination_owner TEXT,form_time TEXT,amount TEXT,bank TEXT,first_seen INTEGER,last_seen INTEGER,status TEXT DEFAULT 'pending',alert_sent INTEGER DEFAULT 0,staff_id INTEGER,assignment_id INTEGER,staff_status TEXT,processed_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
    CREATE TABLE IF NOT EXISTS audit_logs(id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER,action TEXT,detail TEXT,created_at TEXT);
    CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY,value TEXT NOT NULL);
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
      'assignments': [('work_date','TEXT'),('office_id','INTEGER'),('shift_id','INTEGER'),('staff_id','INTEGER'),('channel_id','INTEGER'),('category','TEXT'),('target','TEXT'),('start_time','TEXT'),('end_time','TEXT'),('is_active','INTEGER DEFAULT 1')],
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
 g.user=None
 if session.get('uid'):
  with db_conn() as c:g.user=c.execute('SELECT * FROM users WHERE id=? AND is_active=1',(session['uid'],)).fetchone()

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
   session['uid']=u['id']; c.execute('UPDATE users SET last_login=? WHERE id=?',(now().isoformat(),u['id'])); c.commit(); return redirect(url_for('dashboard'))
 return render_template('login.html')
@app.route('/2fa/verify',methods=['GET','POST'])
def twofa_verify():
 uid=session.get('pending_uid')
 if not uid:return redirect(url_for('login'))
 with db_conn() as c:u=c.execute('SELECT * FROM users WHERE id=?',(uid,)).fetchone()
 if request.method=='POST':
  if totp_verify(u['twofa_secret'],request.form['code'].strip()): session.pop('pending_uid',None); session['uid']=uid; return redirect(url_for('dashboard'))
  flash('Kode 2FA salah.','danger')
 return render_template('twofa.html')
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
  assignments=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,o.name office_name,sh.name shift_name,ch.name channel_name FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id WHERE a.work_date=?'''+(' AND a.office_id=?' if office_id else '')+' ORDER BY o.name,sh.start_time,ch.category,ch.name',(today,office_id) if office_id else (today,)).fetchall()
  leaves=c.execute("SELECT l.*,s.name,s.cs_name,o.name office_name FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.status='OUT'"+(' AND s.office_id=?' if office_id else ''),(office_id,) if office_id else ()).fetchall()
  alerts=c.execute('''SELECT d.*,s.name staff_name,s.cs_name,o.name office_name FROM deposit_forms d LEFT JOIN staff s ON s.id=d.staff_id LEFT JOIN offices o ON o.id=d.office_id WHERE d.alert_sent=1'''+(' AND d.office_id=?' if office_id else '')+' ORDER BY d.id DESC LIMIT 50',(office_id,) if office_id else ()).fetchall()
  stats={'staff':sum(1 for x in staff if x['status']=='Aktif'),'out':len(leaves),'alerts':len(alerts),'ex':sum(1 for x in staff if x['status']=='Ex Karyawan')}
 return render_template('dashboard.html',offices=offices,office_id=office_id,staff=staff,assignments=assignments,leaves=leaves,alerts=alerts,stats=stats)

@app.route('/offices',methods=['GET','POST'])
@roles('superadmin','supervisor')
def offices_page():
 with db_conn() as c:
  if request.method=='POST':
   c.execute('INSERT INTO offices(name,location,status) VALUES(?,?,?) ON CONFLICT(name) DO UPDATE SET location=excluded.location,status=excluded.status',(request.form['name'].strip(),request.form.get('location',''),request.form.get('status','Aktif'))); audit(c,'office.save',request.form['name']); c.commit(); return redirect(url_for('offices_page'))
  rows=c.execute('SELECT * FROM offices ORDER BY name').fetchall()
 return render_template('offices.html',rows=rows)

@app.route('/shifts',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def shifts_page():
 with db_conn() as c:
  if request.method=='POST':
   c.execute('INSERT INTO shifts(office_id,name,code,start_time,end_time,status) VALUES(?,?,?,?,?,?)',(request.form['office_id'],request.form['name'],request.form.get('code',''),request.form['start_time'],request.form['end_time'],request.form.get('status','Aktif'))); c.commit(); return redirect(url_for('shifts_page'))
  rows=c.execute('SELECT sh.*,o.name office_name FROM shifts sh JOIN offices o ON o.id=sh.office_id ORDER BY o.name,sh.start_time').fetchall(); offices=c.execute('SELECT * FROM offices').fetchall()
 return render_template('shifts.html',rows=rows,offices=offices)

@app.route('/channels',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def channels_page():
 with db_conn() as c:
  if request.method=='POST':
   c.execute('INSERT INTO channels(office_id,name,category,aliases,status) VALUES(?,?,?,?,?)',(request.form['office_id'],request.form['name'].strip(),request.form['category'],request.form.get('aliases',''),request.form.get('status','Aktif'))); c.commit(); return redirect(url_for('channels_page'))
  rows=c.execute('SELECT ch.*,o.name office_name FROM channels ch JOIN offices o ON o.id=ch.office_id ORDER BY o.name,ch.category,ch.name').fetchall(); offices=c.execute('SELECT * FROM offices').fetchall()
 return render_template('channels.html',rows=rows,offices=offices)

@app.route('/staff',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def staff_page():
 with db_conn() as c:
  if request.method=='POST':
   f=request.form; sid=f.get('id',type=int); vals=(f['name'].strip(),f.get('telegram_id') or None,f.get('telegram_username',''),f.get('email',''),f.get('agent_code',''),f.get('cs_name',''),f.get('office_id',type=int),f.get('position','CS'),f.get('status','Aktif'),f.get('join_date') or None,f.get('notes',''))
   if sid:c.execute('UPDATE staff SET name=?,telegram_id=?,telegram_username=?,email=?,agent_code=?,cs_name=?,office_id=?,position=?,status=?,join_date=?,notes=? WHERE id=?',vals+(sid,))
   else:sid=c.execute('INSERT INTO staff(name,telegram_id,telegram_username,email,agent_code,cs_name,office_id,position,status,join_date,notes) VALUES(?,?,?,?,?,?,?,?,?,?,?)',vals).lastrowid
   if f.get('login_id'):
    pw=f.get('password') or secrets.token_urlsafe(6); c.execute('INSERT INTO users(username,password_hash,role,staff_id,office_id,is_active,must_change_password) VALUES(?,?,?,?,?,1,1) ON CONFLICT(staff_id) DO UPDATE SET username=excluded.username,office_id=excluded.office_id',(f['login_id'],generate_password_hash(pw),'staff',sid,f.get('office_id',type=int)))
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
   ch=c.execute('SELECT * FROM channels WHERE id=?',(request.form['channel_id'],)).fetchone(); sh=c.execute('SELECT * FROM shifts WHERE id=?',(request.form['shift_id'],)).fetchone()
   c.execute('INSERT INTO assignments(work_date,office_id,shift_id,staff_id,channel_id,category,target,start_time,end_time) VALUES(?,?,?,?,?,?,?,?,?)',(request.form['work_date'],request.form['office_id'],request.form['shift_id'],request.form['staff_id'],request.form['channel_id'],ch['category'],ch['name'],request.form.get('start_time') or sh['start_time'],request.form.get('end_time') or sh['end_time']));c.commit();return redirect(url_for('assignments_page',date=request.form['work_date']))
  date=request.args.get('date') or now().date().isoformat(); rows=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,o.name office_name,sh.name shift_name,ch.name channel_name FROM assignments a JOIN staff s ON s.id=a.staff_id JOIN offices o ON o.id=a.office_id JOIN shifts sh ON sh.id=a.shift_id LEFT JOIN channels ch ON ch.id=a.channel_id WHERE a.work_date=? ORDER BY o.name,sh.start_time,ch.category,ch.name''',(date,)).fetchall(); offices=c.execute('SELECT * FROM offices').fetchall(); shifts=c.execute("SELECT * FROM shifts WHERE status='Aktif'").fetchall(); staff=c.execute("SELECT * FROM staff WHERE status='Aktif'").fetchall(); channels=c.execute("SELECT * FROM channels WHERE status='Aktif'").fetchall()
 return render_template('assignments.html',date=date,rows=rows,offices=offices,shifts=shifts,staff=staff,channels=channels)

@app.route('/inout',methods=['GET','POST'])
@login_required
def inout_page():
 if not g.user['staff_id']: return ('Akun ini tidak terhubung ke Data Staf.',400)
 sid=g.user['staff_id']
 with db_conn() as c:
  staff=c.execute('SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE s.id=?',(sid,)).fetchone(); active=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone(); ass=find_assignment(c,staff['office_id'],'',now())
  if request.method=='POST':
   action=request.form['action']
   if action=='out':
    if active:flash('Kamu masih izin keluar.','danger')
    elif c.execute("SELECT COUNT(*) n FROM leaves WHERE status='OUT'").fetchone()['n']>=MAX_ACTIVE_LEAVES:flash(f'Maksimal {MAX_ACTIVE_LEAVES} orang izin bersamaan.','danger')
    else:
     reason=request.form['reason']; out=now(); exp=out+timedelta(minutes=DURATIONS[reason]); snap=json.dumps({'jobdesk':ass['target'] if ass else '-','cs':staff['cs_name'],'office':staff['office_name']})
     c.execute('INSERT INTO leaves(staff_id,reason,out_at,expected_at,status,source,assignment_snapshot) VALUES(?,?,?,?,?,?,?)',(sid,reason,out.isoformat(),exp.isoformat(),'OUT','dashboard',snap));c.commit();tg_send(INOUT_CHAT_ID,f"🚪 <b>IZIN KELUAR</b>\n👤 {staff['name']} — {staff['cs_name'] or '-'}\n💼 {ass['target'] if ass else '-'}\n📝 {reason.title()}\n⏳ Estimasi kembali: {exp.strftime('%H:%M')} WIB")
   elif action=='in' and active:
    t=now(); exp=datetime.fromisoformat(active['expected_at']); late=max(0,int((t-exp).total_seconds()//60)); fine=late*50000 if 1<=late<=9 else (500000 if late>=10 else 0); c.execute("UPDATE leaves SET in_at=?,status='IN',late_minutes=?,fine=? WHERE id=?",(t.isoformat(),late,fine,active['id']));c.commit();tg_send(INOUT_CHAT_ID,f"✅ <b>SUDAH KEMBALI</b>\n👤 {staff['name']}\n⏱ Terlambat: {late} menit\n💸 Denda: Rp{fine:,}")
   return redirect(url_for('inout_page'))
  history=c.execute('SELECT * FROM leaves WHERE staff_id=? ORDER BY id DESC LIMIT 50',(sid,)).fetchall()
 return render_template('inout.html',staff=staff,active=active,history=history,assignment=ass,durations=DURATIONS)

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
  c.execute('INSERT INTO devices(device_id,device_name,office_id,last_seen,page_url,form_count,late_count) VALUES(?,?,?,?,?,?,?) ON CONFLICT(device_id) DO UPDATE SET device_name=excluded.device_name,office_id=COALESCE(excluded.office_id,devices.office_id),last_seen=excluded.last_seen,page_url=excluded.page_url,form_count=excluded.form_count,late_count=excluded.late_count',(did,name,office_id,int(time.time()),d.get('pageUrl',''),int(d.get('formCount',0)),int(d.get('lateCount',0))));c.commit(); leader=c.execute('SELECT device_id FROM devices WHERE last_seen>=? ORDER BY device_id LIMIT 1',(int(time.time())-LEADER_TTL_SECONDS,)).fetchone()
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
  c.execute('''INSERT INTO deposit_forms(form_id,device_id,office_id,username,game_id,destination,destination_account,destination_owner,form_time,amount,bank,first_seen,last_seen,status,staff_id,assignment_id,staff_status,processed_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(form_id) DO UPDATE SET last_seen=excluded.last_seen,status=excluded.status,staff_id=COALESCE(deposit_forms.staff_id,excluded.staff_id),assignment_id=COALESCE(deposit_forms.assignment_id,excluded.assignment_id),staff_status=excluded.staff_status,processed_at=excluded.processed_at''',(form_id,device_id,office_id,d.get('username'),d.get('gameId'),destination,d.get('destinationAccount'),d.get('destinationOwner'),d.get('formTime'),str(d.get('amount','')),d.get('bank'),first,last,status,sid,ass['id'] if ass else None,staff_status,now().isoformat() if status in ('done','processed','completed') else None))
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
