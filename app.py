import os, json, time, uuid, sqlite3, threading, hashlib, secrets
from datetime import datetime, timedelta
from functools import wraps
from html import escape
from zoneinfo import ZoneInfo

import requests
from flask import Flask, render_template, request, redirect, url_for, session, flash, jsonify, g
from werkzeug.security import generate_password_hash, check_password_hash

WIB = ZoneInfo("Asia/Jakarta")
DB_PATH = os.getenv("DB_PATH", "/data/omtogel_staff.db")
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
INOUT_CHAT_ID = os.getenv("INOUT_CHAT_ID", os.getenv("CHAT_ID", "")).strip()
ALERT_CHAT_ID = os.getenv("ALERT_CHAT_ID", os.getenv("CHAT_ID", "")).strip()
API_KEY = os.getenv("API_KEY", "").strip()
SECRET_KEY = os.getenv("SECRET_KEY", secrets.token_hex(32))
LATE_MINUTES = int(os.getenv("LATE_MINUTES", "5"))
SCAN_SECONDS = int(os.getenv("SCAN_SECONDS", "5"))
LEADER_TTL_SECONDS = int(os.getenv("LEADER_TTL_SECONDS", "15"))
MAX_DEVICES = int(os.getenv("MAX_DEVICES", "0"))
ADMIN_USERNAME = os.getenv("ADMIN_USERNAME", "admin")
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "admin12345")

DURATIONS = {"makan":20, "merokok":10, "toilet":5, "bab":15}
MAX_ACTIVE_LEAVES = 5

app = Flask(__name__)
app.secret_key = SECRET_KEY
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax")
lock = threading.RLock()
_bot_thread_started = False


def now(): return datetime.now(WIB)
def ts(): return int(time.time())
def fmt_dt(v):
    if not v: return "-"
    try: return datetime.fromisoformat(v).astimezone(WIB).strftime("%d-%m-%Y %H:%M:%S")
    except Exception: return str(v)
app.jinja_env.filters["dt"] = fmt_dt


def db_conn():
    d = os.path.dirname(DB_PATH)
    if d: os.makedirs(d, exist_ok=True)
    c = sqlite3.connect(DB_PATH, timeout=30, check_same_thread=False)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA journal_mode=WAL")
    c.execute("PRAGMA foreign_keys=ON")
    c.execute("PRAGMA busy_timeout=30000")
    return c


def init_db():
    with lock, db_conn() as c:
        c.executescript('''
        CREATE TABLE IF NOT EXISTS offices(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT NOT NULL UNIQUE,location TEXT,status TEXT NOT NULL DEFAULT 'aktif');
        CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY AUTOINCREMENT,username TEXT NOT NULL UNIQUE,password_hash TEXT NOT NULL,role TEXT NOT NULL DEFAULT 'staff',staff_id INTEGER,office_id INTEGER,is_active INTEGER NOT NULL DEFAULT 1,allowed_menus TEXT NOT NULL DEFAULT '["my_dashboard","inout"]',device_token TEXT,last_login TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id),FOREIGN KEY(office_id) REFERENCES offices(id));
        CREATE TABLE IF NOT EXISTS staff(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT NOT NULL,telegram_id TEXT UNIQUE,telegram_username TEXT,email TEXT,agent_code TEXT,cs_name TEXT,office_id INTEGER,shift TEXT NOT NULL DEFAULT 'Pagi',position TEXT NOT NULL DEFAULT 'CS',status TEXT NOT NULL DEFAULT 'Aktif',join_date TEXT,notes TEXT,sp_notes TEXT,FOREIGN KEY(office_id) REFERENCES offices(id));
        CREATE TABLE IF NOT EXISTS shifts(id INTEGER PRIMARY KEY AUTOINCREMENT,office_id INTEGER,name TEXT,start_time TEXT,end_time TEXT,UNIQUE(office_id,name),FOREIGN KEY(office_id) REFERENCES offices(id));
        CREATE TABLE IF NOT EXISTS assignments(id INTEGER PRIMARY KEY AUTOINCREMENT,work_date TEXT NOT NULL,office_id INTEGER,shift_id INTEGER,staff_id INTEGER,category TEXT NOT NULL,target TEXT NOT NULL,start_time TEXT,end_time TEXT,is_active INTEGER DEFAULT 1,FOREIGN KEY(office_id) REFERENCES offices(id),FOREIGN KEY(shift_id) REFERENCES shifts(id),FOREIGN KEY(staff_id) REFERENCES staff(id));
        CREATE TABLE IF NOT EXISTS offdays(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER,off_date TEXT NOT NULL,notes TEXT,created_at TEXT,UNIQUE(staff_id,off_date),FOREIGN KEY(staff_id) REFERENCES staff(id));
        CREATE TABLE IF NOT EXISTS leaves(id INTEGER PRIMARY KEY AUTOINCREMENT,staff_id INTEGER NOT NULL,reason TEXT NOT NULL,out_at TEXT NOT NULL,expected_at TEXT NOT NULL,in_at TEXT,status TEXT NOT NULL DEFAULT 'OUT',late_minutes INTEGER DEFAULT 0,fine INTEGER DEFAULT 0,source TEXT DEFAULT 'dashboard',notified_overdue INTEGER DEFAULT 0,assignment_snapshot TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
        CREATE TABLE IF NOT EXISTS devices(device_id TEXT PRIMARY KEY,device_name TEXT NOT NULL,office_id INTEGER,last_seen INTEGER NOT NULL,page_url TEXT,form_count INTEGER DEFAULT 0,late_count INTEGER DEFAULT 0,FOREIGN KEY(office_id) REFERENCES offices(id));
        CREATE TABLE IF NOT EXISTS deposit_alerts(id INTEGER PRIMARY KEY AUTOINCREMENT,form_id TEXT NOT NULL UNIQUE,device_id TEXT,office_id INTEGER,username TEXT,game_id TEXT,destination TEXT,destination_account TEXT,destination_owner TEXT,form_time TEXT,amount TEXT,bank TEXT,age_minutes INTEGER,staff_id INTEGER,assignment_id INTEGER,staff_status TEXT,sent_at TEXT,FOREIGN KEY(staff_id) REFERENCES staff(id));
        CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY,value TEXT NOT NULL);
        ''')
        c.execute("INSERT OR IGNORE INTO offices(name,location) VALUES('Kantor Utama','-')")
        oid = c.execute("SELECT id FROM offices ORDER BY id LIMIT 1").fetchone()[0]
        c.execute("INSERT OR IGNORE INTO shifts(office_id,name,start_time,end_time) VALUES(?,?,?,?)",(oid,'Pagi','06:00','18:00'))
        c.execute("INSERT OR IGNORE INTO shifts(office_id,name,start_time,end_time) VALUES(?,?,?,?)",(oid,'Malam','18:00','06:00'))
        c.execute("INSERT OR IGNORE INTO settings(key,value) VALUES('late_minutes',?)",(str(LATE_MINUTES),))
        if not c.execute("SELECT 1 FROM users WHERE username=?",(ADMIN_USERNAME,)).fetchone():
            c.execute("INSERT INTO users(username,password_hash,role,office_id,allowed_menus) VALUES(?,?,?,?,?)",(ADMIN_USERNAME,generate_password_hash(ADMIN_PASSWORD),'superadmin',oid,json.dumps(['*'])))
        c.commit()


@app.before_request
def before():
    g.user = None
    uid = session.get('uid')
    if uid:
        with db_conn() as c: g.user = c.execute("SELECT * FROM users WHERE id=? AND is_active=1",(uid,)).fetchone()


def login_required(fn):
    @wraps(fn)
    def w(*a,**k):
        if not g.user: return redirect(url_for('login'))
        return fn(*a,**k)
    return w


def roles(*allowed):
    def deco(fn):
        @wraps(fn)
        def w(*a,**k):
            if not g.user: return redirect(url_for('login'))
            if g.user['role'] not in allowed: return ("Akses ditolak",403)
            return fn(*a,**k)
        return w
    return deco


def office_scope_sql(alias='s'):
    if g.user and g.user['role'] not in ('superadmin','supervisor') and g.user['office_id']:
        return f" AND {alias}.office_id={int(g.user['office_id'])}"
    return ''


def tg_send(chat_id,text,reply_markup=None):
    if not BOT_TOKEN or not chat_id: return False
    payload={"chat_id":chat_id,"text":text,"parse_mode":"HTML","disable_web_page_preview":True}
    if reply_markup: payload['reply_markup']=reply_markup
    r=requests.post(f"https://api.telegram.org/bot{BOT_TOKEN}/sendMessage",json=payload,timeout=20)
    return r.ok and r.json().get('ok')


def current_assignment(c, staff_id=None, office_id=None, target=None, when=None):
    when=when or now(); date=when.date().isoformat(); hm=when.strftime('%H:%M')
    q='''SELECT a.*,s.name staff_name,s.cs_name,s.agent_code,s.status staff_status,o.name office_name,o.location,sh.name shift_name
         FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id
         WHERE a.work_date=? AND a.is_active=1'''
    p=[date]
    if staff_id: q+=' AND a.staff_id=?'; p.append(staff_id)
    if office_id: q+=' AND a.office_id=?'; p.append(office_id)
    rows=c.execute(q,p).fetchall()
    def active(r):
        st=r['start_time'] or '00:00'; en=r['end_time'] or '23:59'
        ok=(st<=hm<=en) if st<=en else (hm>=st or hm<=en)
        if target:
            hay=' '.join([r['category'] or '',r['target'] or '']).lower(); needles=[x for x in target.lower().replace('-',' ').split() if len(x)>1]
            ok=ok and (target.lower() in hay or any(x in hay for x in needles))
        return ok
    matches=[r for r in rows if active(r)]
    return matches[0] if matches else None


def staff_snapshot(c, staff_id):
    s=c.execute('''SELECT s.*,o.name office_name,o.location FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE s.id=?''',(staff_id,)).fetchone()
    a=current_assignment(c,staff_id=staff_id)
    return s,a


@app.route('/login',methods=['GET','POST'])
def login():
    if request.method=='POST':
        ua=request.headers.get('User-Agent','').lower()
        if any(x in ua for x in ['android','iphone','ipad','mobile']):
            flash('Login staf hanya diizinkan dari PC.','danger'); return render_template('login.html')
        with db_conn() as c:
            u=c.execute("SELECT * FROM users WHERE username=? AND is_active=1",(request.form['username'].strip(),)).fetchone()
            if not u or not check_password_hash(u['password_hash'],request.form['password']):
                flash('Username atau password salah.','danger'); return render_template('login.html')
            browser_token=request.cookies.get('omt_device')
            if u['role']=='staff' and u['device_token'] and browser_token!=u['device_token']:
                flash('Akun ini terikat ke PC lain. Hubungi leader untuk reset perangkat.','danger'); return render_template('login.html')
            if u['role']=='staff' and not u['device_token']:
                browser_token=secrets.token_urlsafe(32); c.execute("UPDATE users SET device_token=? WHERE id=?",(browser_token,u['id']))
            c.execute("UPDATE users SET last_login=? WHERE id=?",(now().isoformat(),u['id'])); c.commit()
        session['uid']=u['id']; resp=redirect(url_for('dashboard'))
        if browser_token: resp.set_cookie('omt_device',browser_token,max_age=31536000,httponly=True,samesite='Lax')
        return resp
    return render_template('login.html')

@app.get('/logout')
def logout(): session.clear(); return redirect(url_for('login'))

@app.get('/')
@login_required
def dashboard():
    with db_conn() as c:
        today=now().date().isoformat(); scope=office_scope_sql('s')
        stats={
          'staff':c.execute("SELECT COUNT(*) n FROM staff s WHERE status='Aktif'"+scope).fetchone()['n'],
          'out':c.execute("SELECT COUNT(*) n FROM leaves l JOIN staff s ON s.id=l.staff_id WHERE l.status='OUT'"+scope).fetchone()['n'],
          'alerts':c.execute("SELECT COUNT(*) n FROM deposit_alerts d LEFT JOIN staff s ON s.id=d.staff_id WHERE substr(d.sent_at,1,10)=?"+scope,(today,)).fetchone()['n'],
          'off':c.execute("SELECT COUNT(*) n FROM offdays o JOIN staff s ON s.id=o.staff_id WHERE o.off_date=?"+scope,(today,)).fetchone()['n']}
        assignments=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,o.name office_name,sh.name shift_name,
          (SELECT status FROM leaves l WHERE l.staff_id=s.id AND l.status='OUT' ORDER BY id DESC LIMIT 1) leave_status
          FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id
          WHERE a.work_date=?'''+office_scope_sql('s')+''' ORDER BY o.name,sh.name,a.category,a.target''',(today,)).fetchall()
        active_leaves=c.execute('''SELECT l.*,s.name,s.cs_name,o.name office_name FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.status='OUT' '''+office_scope_sql('s')+''' ORDER BY l.out_at''').fetchall()
        alerts=c.execute('''SELECT d.*,s.name staff_name,s.cs_name,o.name office_name FROM deposit_alerts d LEFT JOIN staff s ON s.id=d.staff_id LEFT JOIN offices o ON o.id=d.office_id WHERE substr(d.sent_at,1,10)=?'''+office_scope_sql('s')+''' ORDER BY d.id DESC LIMIT 30''',(today,)).fetchall()
    return render_template('dashboard.html',stats=stats,assignments=assignments,active_leaves=active_leaves,alerts=alerts,now=now())

@app.route('/staff',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def staff_page():
    with db_conn() as c:
        if request.method=='POST':
            f=request.form; sid=f.get('id') or None
            vals=(f['name'].strip(),f.get('telegram_id') or None,f.get('telegram_username',''),f.get('email',''),f.get('agent_code',''),f.get('cs_name',''),int(f['office_id']),f.get('shift','Pagi'),f.get('position','CS'),f.get('status','Aktif'),f.get('join_date') or None,f.get('notes',''),f.get('sp_notes',''))
            try:
                if sid: c.execute('''UPDATE staff SET name=?,telegram_id=?,telegram_username=?,email=?,agent_code=?,cs_name=?,office_id=?,shift=?,position=?,status=?,join_date=?,notes=?,sp_notes=? WHERE id=?''',vals+(sid,))
                else: c.execute('''INSERT INTO staff(name,telegram_id,telegram_username,email,agent_code,cs_name,office_id,shift,position,status,join_date,notes,sp_notes) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)''',vals)
                c.commit(); flash('Data staf tersimpan.','success')
            except sqlite3.IntegrityError as e: flash(f'Gagal: Telegram ID sudah dipakai. {e}','danger')
            return redirect(url_for('staff_page'))
        rows=c.execute('''SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE 1=1'''+office_scope_sql('s')+' ORDER BY s.name').fetchall()
        offices=c.execute("SELECT * FROM offices WHERE status='aktif' ORDER BY name").fetchall()
    return render_template('staff.html',rows=rows,offices=offices)

@app.post('/staff/delete/<int:sid>')
@roles('superadmin')
def staff_delete(sid):
    with db_conn() as c:
        c.execute("UPDATE staff SET status='Resign' WHERE id=?",(sid,)); c.execute("UPDATE users SET is_active=0 WHERE staff_id=?",(sid,)); c.commit()
    return redirect(url_for('staff_page'))

@app.route('/offices',methods=['GET','POST'])
@roles('superadmin','supervisor')
def offices_page():
    with db_conn() as c:
        if request.method=='POST':
            oid=request.form.get('id'); vals=(request.form['name'].strip(),request.form.get('location','').strip(),request.form.get('status','aktif'))
            if oid: c.execute("UPDATE offices SET name=?,location=?,status=? WHERE id=?",vals+(oid,))
            else: c.execute("INSERT INTO offices(name,location,status) VALUES(?,?,?)",vals)
            c.commit(); return redirect(url_for('offices_page'))
        rows=c.execute("SELECT * FROM offices ORDER BY name").fetchall()
    return render_template('offices.html',rows=rows)

@app.route('/assignments',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def assignments_page():
    with db_conn() as c:
        if request.method=='POST':
            f=request.form; aid=f.get('id'); vals=(f['work_date'],int(f['office_id']),int(f['shift_id']),int(f['staff_id']),f['category'],f['target'].strip(),f['start_time'],f['end_time'],1)
            if aid: c.execute('''UPDATE assignments SET work_date=?,office_id=?,shift_id=?,staff_id=?,category=?,target=?,start_time=?,end_time=?,is_active=? WHERE id=?''',vals+(aid,))
            else: c.execute('''INSERT INTO assignments(work_date,office_id,shift_id,staff_id,category,target,start_time,end_time,is_active) VALUES(?,?,?,?,?,?,?,?,?)''',vals)
            c.commit(); return redirect(url_for('assignments_page',date=f['work_date']))
        date=request.args.get('date',now().date().isoformat())
        rows=c.execute('''SELECT a.*,s.name staff_name,s.cs_name,o.name office_name,sh.name shift_name FROM assignments a JOIN staff s ON s.id=a.staff_id LEFT JOIN offices o ON o.id=a.office_id LEFT JOIN shifts sh ON sh.id=a.shift_id WHERE a.work_date=?'''+office_scope_sql('s')+' ORDER BY o.name,sh.name,a.category,a.target',(date,)).fetchall()
        staff=c.execute("SELECT * FROM staff s WHERE status='Aktif'"+office_scope_sql('s')+' ORDER BY name').fetchall(); offices=c.execute("SELECT * FROM offices WHERE status='aktif' ORDER BY name").fetchall(); shifts=c.execute("SELECT * FROM shifts ORDER BY office_id,name").fetchall()
    return render_template('assignments.html',rows=rows,staff=staff,offices=offices,shifts=shifts,date=date)

@app.post('/assignments/delete/<int:aid>')
@roles('superadmin','supervisor','leader')
def assignment_delete(aid):
    with db_conn() as c: c.execute("DELETE FROM assignments WHERE id=?",(aid,)); c.commit()
    return redirect(request.referrer or url_for('assignments_page'))

@app.route('/offdays',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def offdays_page():
    with db_conn() as c:
        if request.method=='POST':
            c.execute("INSERT OR REPLACE INTO offdays(staff_id,off_date,notes,created_at) VALUES(?,?,?,?)",(int(request.form['staff_id']),request.form['off_date'],request.form.get('notes',''),now().isoformat())); c.commit(); return redirect(url_for('offdays_page'))
        rows=c.execute('''SELECT o.*,s.name,s.cs_name,ofc.name office_name FROM offdays o JOIN staff s ON s.id=o.staff_id LEFT JOIN offices ofc ON ofc.id=s.office_id WHERE o.off_date>=?'''+office_scope_sql('s')+''' ORDER BY o.off_date,s.name''',(now().date().isoformat(),)).fetchall(); staff=c.execute("SELECT * FROM staff s WHERE status='Aktif'"+office_scope_sql('s')+' ORDER BY name').fetchall()
    return render_template('offdays.html',rows=rows,staff=staff)

@app.route('/users',methods=['GET','POST'])
@roles('superadmin','supervisor','leader')
def users_page():
    with db_conn() as c:
        if request.method=='POST':
            f=request.form; menus=f.getlist('menus'); sid=int(f['staff_id']); s=c.execute("SELECT * FROM staff WHERE id=?",(sid,)).fetchone();
            if not s: flash('Staf tidak ditemukan','danger'); return redirect(url_for('users_page'))
            role=f.get('role','staff'); username=f['username'].strip(); pwd=f.get('password','')
            existing=c.execute("SELECT * FROM users WHERE staff_id=?",(sid,)).fetchone()
            if existing:
                q="UPDATE users SET username=?,role=?,office_id=?,allowed_menus=?,is_active=?"; p=[username,role,s['office_id'],json.dumps(menus),1 if f.get('is_active') else 0]
                if pwd: q+=",password_hash=?"; p.append(generate_password_hash(pwd))
                q+=" WHERE id=?"; p.append(existing['id']); c.execute(q,p)
            else:
                if not pwd: flash('Password wajib untuk akun baru','danger'); return redirect(url_for('users_page'))
                c.execute("INSERT INTO users(username,password_hash,role,staff_id,office_id,allowed_menus,is_active) VALUES(?,?,?,?,?,?,?)",(username,generate_password_hash(pwd),role,sid,s['office_id'],json.dumps(menus),1))
            c.commit(); flash('Akses akun tersimpan.','success'); return redirect(url_for('users_page'))
        rows=c.execute('''SELECT u.*,s.name staff_name,o.name office_name FROM users u LEFT JOIN staff s ON s.id=u.staff_id LEFT JOIN offices o ON o.id=u.office_id ORDER BY u.username''').fetchall(); staff=c.execute("SELECT * FROM staff s WHERE status='Aktif'"+office_scope_sql('s')+' ORDER BY name').fetchall()
    return render_template('users.html',rows=rows,staff=staff)

@app.post('/users/reset-device/<int:uid>')
@roles('superadmin','supervisor','leader')
def reset_device(uid):
    with db_conn() as c: c.execute("UPDATE users SET device_token=NULL WHERE id=?",(uid,)); c.commit()
    flash('Ikatan PC berhasil direset.','success'); return redirect(url_for('users_page'))

@app.route('/inout',methods=['GET','POST'])
@login_required
def inout_page():
    if not g.user['staff_id'] and g.user['role']=='staff': return ('Akun belum terhubung ke Data Staf',400)
    sid=int(request.form.get('staff_id') or g.user['staff_id'] or 0)
    if request.method=='POST':
        action=request.form.get('action')
        with lock, db_conn() as c:
            if action=='out':
                reason=request.form['reason'];
                if reason not in DURATIONS: flash('Alasan izin tidak valid.','danger'); return redirect(url_for('inout_page'))
                if c.execute("SELECT 1 FROM leaves WHERE staff_id=? AND status='OUT'",(sid,)).fetchone(): flash('Staf masih berstatus izin keluar.','danger'); return redirect(url_for('inout_page'))
                active=c.execute("SELECT COUNT(*) n FROM leaves WHERE status='OUT'").fetchone()['n']
                if active>=MAX_ACTIVE_LEAVES: flash('Maksimal 5 orang boleh izin bersamaan.','danger'); return redirect(url_for('inout_page'))
                s,a=staff_snapshot(c,sid); out=now(); exp=out+timedelta(minutes=DURATIONS[reason]); snap=json.dumps(dict(a) if a else {},default=str)
                c.execute("INSERT INTO leaves(staff_id,reason,out_at,expected_at,source,assignment_snapshot) VALUES(?,?,?,?,?,?)",(sid,reason,out.isoformat(),exp.isoformat(),'dashboard',snap)); c.commit()
                send_leave_message(c,sid,reason,out,exp,False); flash('Izin keluar berhasil.','success')
            elif action=='in':
                close_leave(c,sid,'dashboard'); flash('Status kembali bekerja berhasil.','success')
        return redirect(url_for('inout_page'))
    with db_conn() as c:
        staff_list=c.execute("SELECT * FROM staff s WHERE status='Aktif'"+office_scope_sql('s')+' ORDER BY name').fetchall() if g.user['role']!='staff' else []
        active=c.execute('''SELECT l.*,s.name,s.cs_name,o.name office_name FROM leaves l JOIN staff s ON s.id=l.staff_id LEFT JOIN offices o ON o.id=s.office_id WHERE l.status='OUT' '''+office_scope_sql('s')+' ORDER BY l.out_at').fetchall()
        history=c.execute('''SELECT l.*,s.name,s.cs_name FROM leaves l JOIN staff s ON s.id=l.staff_id WHERE 1=1 '''+office_scope_sql('s')+' ORDER BY l.id DESC LIMIT 100').fetchall()
    return render_template('inout.html',active=active,history=history,staff_list=staff_list,durations=DURATIONS)


def send_leave_message(c,sid,reason,out,exp,is_telegram):
    s,a=staff_snapshot(c,sid); job=f"{a['category']} — {a['target']}" if a else '-'
    text=(f"🚪 <b>IZIN KELUAR</b>\n\n👤 Nama Staf: <b>{escape(s['name'])}</b>\n🎧 Nama CS: <b>{escape(s['cs_name'] or '-')}</b>\n🏢 Kantor: <b>{escape(s['office_name'] or '-')}</b>\n🌗 Shift: <b>{escape(s['shift'] or '-')}</b>\n💼 Jobdesk: <b>{escape(job)}</b>\n\n📝 Keperluan: <b>{escape(reason.upper())}</b>\n🕒 Jam keluar: <b>{out.strftime('%H:%M')}</b> WIB\n⏳ Estimasi kembali: <b>{exp.strftime('%H:%M')}</b> WIB")
    tg_send(INOUT_CHAT_ID,text,{"inline_keyboard":[[{"text":"✅ Saya Sudah Kembali","callback_data":f"in_{s['telegram_id']}"}]]} if s['telegram_id'] else None)


def close_leave(c,sid,source):
    l=c.execute("SELECT * FROM leaves WHERE staff_id=? AND status='OUT' ORDER BY id DESC LIMIT 1",(sid,)).fetchone()
    if not l: return False
    n=now(); exp=datetime.fromisoformat(l['expected_at']); exp=exp if exp.tzinfo else exp.replace(tzinfo=WIB); late=max(0,int((n-exp).total_seconds()//60)); fine=late*50000 if 1<=late<=9 else (500000 if late>=10 else 0)
    c.execute("UPDATE leaves SET in_at=?,status='IN',late_minutes=?,fine=? WHERE id=?",(n.isoformat(),late,fine,l['id'])); c.commit(); s,a=staff_snapshot(c,sid); dur=int((n-datetime.fromisoformat(l['out_at'])).total_seconds()//60)
    text=f"🟢 <b>STAF SUDAH KEMBALI</b>\n\n👤 {escape(s['name'])} — {escape(s['cs_name'] or '-')}\n📝 {escape(l['reason'].upper())}\n⏱️ Durasi: <b>{dur} menit</b>"
    if fine: text+=f"\n⚠️ Terlambat: <b>{late} menit</b>\n💸 Denda: <b>Rp{fine:,}</b>"
    tg_send(INOUT_CHAT_ID,text); return True

@app.get('/reports')
@roles('superadmin','supervisor','leader')
def reports():
    start=request.args.get('start',(now().date()-timedelta(days=7)).isoformat()); end=request.args.get('end',now().date().isoformat())
    with db_conn() as c:
        pending=c.execute('''SELECT s.name,s.cs_name,o.name office_name,COUNT(d.id) total,MAX(d.age_minutes) max_age,ROUND(AVG(d.age_minutes),1) avg_age FROM staff s LEFT JOIN deposit_alerts d ON d.staff_id=s.id AND substr(d.sent_at,1,10) BETWEEN ? AND ? LEFT JOIN offices o ON o.id=s.office_id WHERE s.status!='Resign' '''+office_scope_sql('s')+''' GROUP BY s.id ORDER BY total DESC,s.name''',(start,end)).fetchall()
        leaves=c.execute('''SELECT s.name,s.cs_name,COUNT(l.id) total_out,COALESCE(SUM(CASE WHEN l.in_at IS NOT NULL THEN CAST((julianday(l.in_at)-julianday(l.out_at))*1440 AS INTEGER) ELSE 0 END),0) total_minutes,COALESCE(SUM(l.fine),0) total_fine FROM staff s LEFT JOIN leaves l ON l.staff_id=s.id AND substr(l.out_at,1,10) BETWEEN ? AND ? WHERE s.status!='Resign' '''+office_scope_sql('s')+''' GROUP BY s.id ORDER BY total_out DESC''',(start,end)).fetchall()
    return render_template('reports.html',pending=pending,leaves=leaves,start=start,end=end)

# Deposit monitor API compatibility

def authorized_api(): return bool(API_KEY) and request.headers.get('X-API-Key','')==API_KEY
@app.get('/health')
@app.get('/api/health')
def health(): return jsonify(status='ok',service='omtogel-staff-integrated',timeWib=now().strftime('%Y-%m-%d %H:%M:%S'),telegramReady=bool(BOT_TOKEN and ALERT_CHAT_ID),apiKeyReady=bool(API_KEY))
@app.post('/api/heartbeat')
def heartbeat():
    if not authorized_api(): return jsonify(ok=False,error='API key tidak valid'),401
    d=request.get_json(silent=True) or {}; did=str(d.get('deviceId','')).strip();
    if not did: return jsonify(ok=False,error='deviceId wajib'),400
    office_id=d.get('officeId')
    with lock,db_conn() as c:
        c.execute('''INSERT INTO devices(device_id,device_name,office_id,last_seen,page_url,form_count,late_count) VALUES(?,?,?,?,?,?,?) ON CONFLICT(device_id) DO UPDATE SET device_name=excluded.device_name,office_id=COALESCE(excluded.office_id,devices.office_id),last_seen=excluded.last_seen,page_url=excluded.page_url,form_count=excluded.form_count,late_count=excluded.late_count''',(did,str(d.get('deviceName') or 'Perangkat'),office_id,ts(),str(d.get('pageUrl','')),int(d.get('formCount',0) or 0),int(d.get('lateCount',0) or 0))); c.commit(); settings={'enabled':True,'lateMinutes':LATE_MINUTES,'scanSeconds':SCAN_SECONDS,'leaderTtlSeconds':LEADER_TTL_SECONDS,'maxDevices':MAX_DEVICES}
    return jsonify(ok=True,isLeader=True,leaderDeviceId=did,settings=settings,serverTimeWib=now().strftime('%Y-%m-%d %H:%M:%S'))

@app.post('/api/form-alert')
def form_alert():
    if not authorized_api(): return jsonify(ok=False,error='API key tidak valid'),401
    d=request.get_json(silent=True) or {}; required=['formId','deviceId','username','formTime','ageMinutes']; missing=[k for k in required if d.get(k) in (None,'')]
    if missing: return jsonify(ok=False,error='Field kurang: '+', '.join(missing)),400
    age=int(d.get('ageMinutes',0));
    if age<LATE_MINUTES: return jsonify(ok=True,sent=False,reason='Belum lewat batas waktu')
    with lock,db_conn() as c:
        if c.execute("SELECT 1 FROM deposit_alerts WHERE form_id=?",(str(d['formId']),)).fetchone(): return jsonify(ok=True,sent=False,reason='Sudah pernah dikirim')
        dev=c.execute("SELECT * FROM devices WHERE device_id=?",(str(d['deviceId']),)).fetchone(); office_id=d.get('officeId') or (dev['office_id'] if dev else None)
        target=' '.join([str(d.get('bank','')),str(d.get('destination','')),str(d.get('destinationOwner',''))])
        a=current_assignment(c,office_id=office_id,target=target)
        sid=a['staff_id'] if a else None; staff_status='Aktif'
        if sid and c.execute("SELECT 1 FROM leaves WHERE staff_id=? AND status='OUT'",(sid,)).fetchone(): staff_status='IZIN KELUAR'
        c.execute('''INSERT INTO deposit_alerts(form_id,device_id,office_id,username,game_id,destination,destination_account,destination_owner,form_time,amount,bank,age_minutes,staff_id,assignment_id,staff_status,sent_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)''',(str(d['formId']),str(d['deviceId']),office_id,str(d['username']),str(d.get('gameId','-')),str(d.get('destination','-')),str(d.get('destinationAccount','-')),str(d.get('destinationOwner','-')),str(d['formTime']),str(d.get('amount','-')),str(d.get('bank','-')),age,sid,a['id'] if a else None,staff_status,now().isoformat())); c.commit()
        s=c.execute("SELECT s.*,o.name office_name FROM staff s LEFT JOIN offices o ON o.id=s.office_id WHERE s.id=?",(sid,)).fetchone() if sid else None
    msg="⚠️ <b>FORM DEPOSIT TERLAMBAT</b>\n\n"
    msg+=f"🏢 Kantor: <b>{escape((s['office_name'] if s else '-') or '-')}</b>\n👤 Staf: <b>{escape((s['name'] if s else 'BELUM TERHUBUNG') or '-')}</b>\n🎧 Nama CS: <b>{escape((s['cs_name'] if s else '-') or '-')}</b>\n💼 Jobdesk: <b>{escape((a['target'] if a else '-') or '-')}</b>\n📌 Status staf: <b>{escape(staff_status)}</b>\n\n🏦 Bank/Tujuan: <b>{escape(target.strip() or '-')}</b>\n🆔 ID: <b>{escape(str(d['username']))}</b>\n🕒 Waktu form: <b>{escape(str(d['formTime']))}</b>\n⏳ Umur form: <b>{age} menit</b>\n💰 Amount: <b>{escape(str(d.get('amount','-')))}</b>"
    tg_send(ALERT_CHAT_ID,msg); return jsonify(ok=True,sent=True,staffId=sid)

@app.get('/api/status')
def api_status():
    if not authorized_api(): return jsonify(ok=False,error='API key tidak valid'),401
    with db_conn() as c: devices=[dict(x) for x in c.execute("SELECT * FROM devices ORDER BY device_name")]; sent=c.execute("SELECT COUNT(*) n FROM deposit_alerts").fetchone()['n']
    for x in devices: x['online']=x['last_seen']>=ts()-LEADER_TTL_SECONDS
    return jsonify(ok=True,devices=devices,sentForms=sent,settings={'enabled':True,'lateMinutes':LATE_MINUTES,'scanSeconds':SCAN_SECONDS,'leaderTtlSeconds':LEADER_TTL_SECONDS,'maxDevices':MAX_DEVICES})

# raw Telegram polling

def bot_loop():
    if not BOT_TOKEN: return
    offset=0
    while True:
        try:
            r=requests.get(f"https://api.telegram.org/bot{BOT_TOKEN}/getUpdates",params={'timeout':25,'offset':offset,'allowed_updates':json.dumps(['message','callback_query'])},timeout=35).json()
            for u in r.get('result',[]):
                offset=u['update_id']+1
                if 'message' in u: handle_tg_message(u['message'])
                elif 'callback_query' in u: handle_tg_callback(u['callback_query'])
        except Exception as e: print('telegram polling error:',e,flush=True); time.sleep(5)

def handle_tg_message(m):
    chat=str(m['chat']['id']); text=(m.get('text') or '').strip().lower(); user=m.get('from',{})
    if INOUT_CHAT_ID and chat!=str(INOUT_CHAT_ID): return
    if text in ['/start','izin','menu']:
        kb={'inline_keyboard':[[{'text':'🍽️ Makan','callback_data':'izin_makan'},{'text':'🚬 Merokok','callback_data':'izin_merokok'}],[{'text':'🚽 Toilet','callback_data':'izin_toilet'},{'text':'💩 BAB','callback_data':'izin_bab'}]]}
        tg_send(chat,'Silakan pilih jenis izin keluar:',kb)
    elif text=='/id': tg_send(chat,f"ID kamu: <code>{user.get('id')}</code>")

def answer_callback(cid,text=''):
    try: requests.post(f"https://api.telegram.org/bot{BOT_TOKEN}/answerCallbackQuery",json={'callback_query_id':cid,'text':text},timeout=10)
    except: pass

def handle_tg_callback(q):
    answer_callback(q['id']); data=q.get('data',''); uid=str(q.get('from',{}).get('id')); chat=str(q['message']['chat']['id'])
    if INOUT_CHAT_ID and chat!=str(INOUT_CHAT_ID): return
    with lock,db_conn() as c:
        s=c.execute("SELECT * FROM staff WHERE telegram_id=? AND status='Aktif'",(uid,)).fetchone()
        if not s: tg_send(chat,'❌ Telegram ID belum terhubung ke Data Staf.'); return
        if data.startswith('izin_'):
            reason=data.replace('izin_','')
            if reason not in DURATIONS: return
            if c.execute("SELECT 1 FROM leaves WHERE staff_id=? AND status='OUT'",(s['id'],)).fetchone(): tg_send(chat,'⚠️ Kamu masih dalam status izin.'); return
            if c.execute("SELECT COUNT(*) n FROM leaves WHERE status='OUT'").fetchone()['n']>=MAX_ACTIVE_LEAVES: tg_send(chat,'❌ Maksimal 5 orang boleh izin bersamaan.'); return
            out=now(); exp=out+timedelta(minutes=DURATIONS[reason]); a=current_assignment(c,staff_id=s['id']); c.execute("INSERT INTO leaves(staff_id,reason,out_at,expected_at,source,assignment_snapshot) VALUES(?,?,?,?,?,?)",(s['id'],reason,out.isoformat(),exp.isoformat(),'telegram',json.dumps(dict(a) if a else {},default=str))); c.commit(); send_leave_message(c,s['id'],reason,out,exp,True)
        elif data.startswith('in_'):
            owner=data.replace('in_','')
            if owner!=uid: tg_send(chat,'❌ Tombol ini hanya untuk pemilik izin.'); return
            if not close_leave(c,s['id'],'telegram'): tg_send(chat,'❌ Data izin aktif tidak ditemukan.')

def overdue_loop():
    while True:
        try:
            with lock,db_conn() as c:
                rows=c.execute("SELECT l.*,s.name,s.cs_name FROM leaves l JOIN staff s ON s.id=l.staff_id WHERE l.status='OUT' AND l.notified_overdue=0").fetchall(); n=now()
                for l in rows:
                    exp=datetime.fromisoformat(l['expected_at']); exp=exp if exp.tzinfo else exp.replace(tzinfo=WIB)
                    if n>exp+timedelta(minutes=10):
                        tg_send(INOUT_CHAT_ID,f"🔴 <b>STAF BELUM KEMBALI</b>\n\n👤 {escape(l['name'])} — {escape(l['cs_name'] or '-')}\n📝 {escape(l['reason'].upper())}\n⏳ Terlambat 10 menit atau lebih\n💸 Denda sementara: <b>Rp500.000</b>")
                        c.execute("UPDATE leaves SET notified_overdue=1,late_minutes=10,fine=500000 WHERE id=?",(l['id'],))
                c.commit()
        except Exception as e: print('overdue loop error',e,flush=True)
        time.sleep(60)

def start_background():
    global _bot_thread_started
    if _bot_thread_started: return
    _bot_thread_started=True
    threading.Thread(target=bot_loop,daemon=True).start(); threading.Thread(target=overdue_loop,daemon=True).start()

init_db(); start_background()
