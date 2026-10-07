"""
Aplikasi Kriptografi Klasik (Flask) - Shift, Substitution, Affine, Vigenere,
Hill, Permutation, One-Time Pad.

Jalankan:  pip install flask  ->  python app.py  ->  buka http://127.0.0.1:5000

Rancangan:
- Mode teks : hanya huruf A-Z yang diproses (angka/spasi/tanda baca dibuang), modulus 26.
- Mode file : setiap byte (termasuk header) diproses dengan modulus 256 (generalisasi cipher).
  Ciphertext file menyimpan nama file asli, sehingga saat dekripsi file kembali ke ekstensi semula.
"""
import math
import random
import re
import secrets
import struct
from io import BytesIO
from urllib.parse import quote

from flask import Flask, jsonify, render_template_string, request, send_file

app = Flask(__name__)
MAGIC = b"CPH1"


class KeyError_(Exception):
    pass


# ---------------------------------------------------------------- parsing kunci
def det_mod(m, M):
    n = len(m)
    if n == 1:
        return m[0][0] % M
    total = 0
    for j in range(n):
        minor = [row[:j] + row[j + 1:] for row in m[1:]]
        total += (-1) ** j * m[0][j] * det_mod(minor, M)
    return total % M


def inv_matrix(m, M):
    n = len(m)
    d = det_mod(m, M)
    if math.gcd(d, M) != 1:
        raise KeyError_(f"Matriks tidak punya balikan modulo {M} (determinan={d}, harus relatif prima dengan {M}).")
    di = pow(d, -1, M)
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            minor = [r[:i] + r[i + 1:] for k, r in enumerate(m) if k != j]
            adj[i][j] = (-1) ** (i + j) * (det_mod(minor, M) if n > 1 else 1)
    return [[(di * adj[i][j]) % M for j in range(n)] for i in range(n)]


def parse_key(cipher, key, M, keyfile):
    key = key or ""
    letters = [ord(c) - 65 for c in key.upper() if "A" <= c <= "Z"]
    nums = [int(x) for x in re.findall(r"-?\d+", key)]
    if cipher == "shift":
        if not nums:
            raise KeyError_("Kunci Shift berupa bilangan bulat.")
        return nums[0] % M
    if cipher == "affine":
        if len(nums) < 2:
            raise KeyError_("Kunci Affine: dua bilangan 'a,b'.")
        a, b = nums[0] % M, nums[1] % M
        if math.gcd(a, M) != 1:
            raise KeyError_(f"a harus relatif prima dengan {M}.")
        return a, b
    if cipher == "vigenere":
        k = letters if M == 26 else list(key.encode("utf-8"))
        if not k:
            raise KeyError_("Kunci Vigenere tidak boleh kosong.")
        return k
    if cipher == "substitution":
        if M == 26:
            seen = []
            for c in letters + list(range(26)):
                if c not in seen:
                    seen.append(c)
            if not letters:
                raise KeyError_("Isi kunci: 26 huruf permutasi atau kata kunci.")
            return seen
        if len(nums) == 256 and sorted(nums) == list(range(256)):
            return nums
        if not key:
            raise KeyError_("Kunci tidak boleh kosong.")
        t = list(range(256))
        random.Random(key).shuffle(t)
        return t
    if cipher == "hill":
        vals = nums if nums else letters
        n = math.isqrt(len(vals))
        if n < 2 or n * n != len(vals):
            raise KeyError_("Kunci Hill: n*n bilangan (mis. '3 3 2 5 7 1 2 3 4') atau n*n huruf (mis. 'GYBNQKURP').")
        mat = [[vals[i * n + j] % M for j in range(n)] for i in range(n)]
        return mat, inv_matrix(mat, M)
    if cipher == "permutation":
        if nums:
            if sorted(nums) != list(range(1, len(nums) + 1)):
                raise KeyError_("Kunci permutasi angka harus permutasi dari 1..n, mis. '3 1 4 2'.")
            return [x - 1 for x in nums]
        if not letters:
            raise KeyError_("Kunci permutasi: urutan angka atau kata kunci.")
        return sorted(range(len(letters)), key=lambda i: (letters[i], i))
    if cipher == "otp":
        if not keyfile:
            raise KeyError_("Unggah file kunci One-Time Pad.")
        if M == 26:
            return [c - 65 for c in keyfile.upper() if 65 <= c <= 90]
        return list(keyfile)
    raise KeyError_("Cipher tidak dikenal.")


# ---------------------------------------------------------------- cipher (data = list int mod M)
def run(cipher, data, k, M, enc):
    s = 1 if enc else -1
    pad = 23 if M == 26 else 0
    if cipher == "shift":
        return [(x + s * k) % M for x in data]
    if cipher == "affine":
        a, b = k
        if enc:
            return [(a * x + b) % M for x in data]
        ai = pow(a, -1, M)
        return [(ai * (x - b)) % M for x in data]
    if cipher == "vigenere":
        return [(x + s * k[i % len(k)]) % M for i, x in enumerate(data)]
    if cipher == "substitution":
        if enc:
            return [k[x] for x in data]
        inv = [0] * M
        for i, v in enumerate(k):
            inv[v] = i
        return [inv[x] for x in data]
    if cipher == "hill":
        mat = k[0] if enc else k[1]
        n = len(mat)
        data = data + [pad] * (-len(data) % n)
        out = []
        for i in range(0, len(data), n):
            blk = data[i:i + n]
            out += [sum(mat[r][c] * blk[c] for c in range(n)) % M for r in range(n)]
        return out
    if cipher == "permutation":
        n = len(k)
        data = data + [pad] * (-len(data) % n)
        out = []
        for i in range(0, len(data), n):
            blk = data[i:i + n]
            if enc:
                out += [blk[k[j]] for j in range(n)]
            else:
                res = [0] * n
                for j in range(n):
                    res[k[j]] = blk[j]
                out += res
        return out
    if cipher == "otp":
        if len(k) < len(data):
            raise KeyError_(f"File kunci terlalu pendek: butuh {len(data)}, tersedia {len(k)}.")
        return [(x + s * k[i]) % M for i, x in enumerate(data)]


# ---------------------------------------------------------------- endpoint
@app.route("/process", methods=["POST"])
def process():
    f = request.form
    cipher, enc = f.get("cipher"), f.get("mode") == "encrypt"
    try:
        kf = request.files.get("keyfile")
        keyfile = kf.read() if kf and kf.filename else None
        if f.get("input_type") == "file":
            up = request.files.get("file")
            if not up or not up.filename:
                raise KeyError_("Pilih file terlebih dahulu.")
            raw, name = up.read(), up.filename
            k = parse_key(cipher, f.get("key"), 256, keyfile)
            if enc:
                nb = name.encode("utf-8")
                body = bytes(run(cipher, list(raw), k, 256, True))
                blob = MAGIC + struct.pack(">H", len(nb)) + nb + struct.pack(">Q", len(raw)) + body
                out_name = name + ".dat"
            else:
                if raw[:4] != MAGIC:
                    raise KeyError_("File bukan ciphertext dari aplikasi ini.")
                nl = struct.unpack(">H", raw[4:6])[0]
                out_name = raw[6:6 + nl].decode("utf-8")
                olen = struct.unpack(">Q", raw[6 + nl:14 + nl])[0]
                body = list(raw[14 + nl:])
                blob = bytes(run(cipher, body, k, 256, False))[:olen]
            resp = send_file(BytesIO(blob), mimetype="application/octet-stream",
                             as_attachment=True, download_name="hasil.bin")
            resp.headers["X-Filename"] = quote(out_name)
            resp.headers["Access-Control-Expose-Headers"] = "X-Filename"
            return resp
        # mode teks
        text = f.get("text", "")
        data = [ord(c) - 65 for c in text.upper() if "A" <= c <= "Z"]
        if not data:
            raise KeyError_("Tidak ada huruf alfabet pada input.")
        k = parse_key(cipher, f.get("key"), 26, keyfile)
        res = "".join(chr(x + 65) for x in run(cipher, data, k, 26, enc))
        plain_clean = "".join(chr(x + 65) for x in data)
        if enc and f.get("group") == "5":
            res = " ".join(res[i:i + 5] for i in range(0, len(res), 5))
        return jsonify(ok=True, input=plain_clean, output=res)
    except KeyError_ as e:
        return jsonify(ok=False, error=str(e)), 400
    except Exception as e:  # noqa
        return jsonify(ok=False, error=f"Kesalahan: {e}"), 400


@app.route("/genkey")
def genkey():
    n = int(request.args.get("n", 50000))
    txt = "".join(secrets.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZ") for _ in range(min(n, 2_000_000)))
    return send_file(BytesIO(txt.encode()), mimetype="text/plain", as_attachment=True, download_name="otp_key.txt")


@app.route("/")
def index():
    return render_template_string(PAGE)


PAGE = r"""<!doctype html><html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Sandi Klasik - Bengkel Cipher</title>
<style>
:root{--bg:#f3f2ff;--ink:#1c1b3a;--mut:#6b6a8c;--line:#dcdaf5;--card:#fff;--acc:#5b43f5;--acc2:#e8e4ff;--mint:#0fa97a;--mint2:#e2f8f0;--bad:#d6336c}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.5 "Segoe UI",system-ui,sans-serif}
.wrap{max-width:1080px;margin:0 auto;padding:22px 18px 60px}
header{display:flex;align-items:center;gap:14px;margin-bottom:6px}
.logo{width:44px;height:44px;position:relative}.logo i{position:absolute;inset:0;border-radius:12px;background:var(--acc)}
.logo i+i{background:var(--mint);transform:rotate(18deg) scale(.72);opacity:.9}
h1{font-size:30px;margin:0;letter-spacing:-.5px}.sub{color:var(--mut);margin:0 0 20px}
.tabs{display:flex;gap:8px;overflow-x:auto;padding:4px 2px 10px}
.tab{flex:0 0 auto;border:1.5px solid var(--line);background:var(--card);border-radius:14px;padding:9px 14px;cursor:pointer;text-align:left;font:inherit;color:var(--ink);transition:.15s}
.tab b{display:block;font-size:14px}.tab span{font-size:12px;color:var(--mut)}
.tab:hover{border-color:var(--acc)}.tab.on{background:var(--acc);border-color:var(--acc);color:#fff}.tab.on span{color:#dcd6ff}
.bar{display:flex;flex-wrap:wrap;gap:12px;align-items:center;margin:8px 0 14px}
.seg{display:inline-flex;background:var(--card);border:1.5px solid var(--line);border-radius:12px;padding:3px}
.seg button{border:0;background:none;padding:7px 16px;border-radius:9px;font:inherit;font-weight:600;color:var(--mut);cursor:pointer}
.seg button.on{background:var(--ink);color:#fff}
.keyrow{background:var(--card);border:1.5px solid var(--line);border-radius:16px;padding:16px;margin-bottom:14px}
.keyrow label{font-weight:600;font-size:14px}.hint{color:var(--mut);font-size:13px;margin:2px 0 8px}
.kin{display:flex;gap:8px;flex-wrap:wrap}
input[type=text],select,textarea{border:1.5px solid var(--line);border-radius:10px;padding:10px 12px;font:inherit;background:#fff;color:var(--ink);outline:none}
input[type=text]{flex:1;min-width:200px;font-family:Consolas,monospace}
input:focus,textarea:focus,select:focus,.tab:focus-visible,button:focus-visible{border-color:var(--acc);box-shadow:0 0 0 3px #5b43f533}
.btn{border:0;border-radius:10px;padding:10px 16px;font:inherit;font-weight:600;cursor:pointer;background:var(--acc2);color:var(--acc)}
.btn:hover{filter:brightness(.96)}.go{background:var(--acc);color:#fff;font-size:16px;padding:12px 28px}
.strip{margin-top:12px;overflow-x:auto}.strip table{border-collapse:separate;border-spacing:3px;font:600 13px Consolas,monospace}
.strip td{width:26px;height:28px;text-align:center;border-radius:6px}.strip tr:first-child td{background:var(--acc2);color:var(--acc)}
.strip tr+tr td{background:var(--mint2);color:var(--mint)}.strip th{font:600 12px "Segoe UI";color:var(--mut);padding-right:8px;text-align:right}
.grid{display:grid;grid-template-columns:1fr 1fr;gap:14px}
.pane{background:var(--card);border:1.5px solid var(--line);border-radius:16px;padding:16px;display:flex;flex-direction:column;min-height:300px}
.pane.out{background:linear-gradient(180deg,#fff,var(--mint2))}
.ph{display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:10px;font-weight:700}
.ph small{font-weight:500;color:var(--mut)}
textarea{flex:1;min-height:200px;resize:vertical;font-family:Consolas,monospace;letter-spacing:.5px;width:100%}
.drop{flex:1;border:2px dashed var(--line);border-radius:14px;display:flex;flex-direction:column;align-items:center;justify-content:center;text-align:center;padding:20px;cursor:pointer;color:var(--mut);transition:.15s}
.drop.over,.drop:hover{border-color:var(--acc);background:var(--acc2)}.drop b{color:var(--ink);word-break:break-all}.drop input{display:none}
.res{flex:1;font-family:Consolas,monospace;letter-spacing:.8px;word-break:break-all;white-space:pre-wrap;min-height:200px;color:#0b6e51}
.empty{color:var(--mut);font-family:"Segoe UI";letter-spacing:0}
.acts{display:flex;gap:8px;flex-wrap:wrap;margin-top:10px}
.cta{display:flex;justify-content:center;margin:16px 0}
#toast{position:fixed;left:50%;bottom:24px;transform:translateX(-50%) translateY(80px);background:var(--ink);color:#fff;padding:11px 18px;border-radius:12px;transition:.25s;max-width:90vw;z-index:9}
#toast.show{transform:translateX(-50%)}#toast.bad{background:var(--bad)}
.hide{display:none!important}.spin{display:inline-block;width:14px;height:14px;border:2px solid #fff6;border-top-color:#fff;border-radius:50%;animation:r .7s linear infinite;vertical-align:-2px;margin-right:6px}
@keyframes r{to{transform:rotate(360deg)}}
.stats{margin-left:auto;display:flex;gap:18px;font-size:13px;color:var(--mut)}.stats b{font-size:22px;color:var(--acc);margin-right:5px}
.info{background:var(--card);border:1.5px solid var(--line);border-radius:16px;padding:14px 16px;margin:6px 0 12px;display:flex;gap:24px;flex-wrap:wrap;align-items:flex-start}
.info code{display:block;margin-top:6px;background:var(--acc2);color:var(--acc);padding:6px 10px;border-radius:8px;font:600 13px Consolas,monospace}
.info ul{margin:0;padding-left:18px;color:var(--mut);font-size:13px;flex:1;min-width:240px}
.lb{font-size:12px;color:var(--mut);font-weight:600;margin:8px 0 4px;word-break:break-all}
.term{background:#14132b;color:#8cf5c9;border-radius:10px;padding:10px 12px;margin:0;font:13px/1.5 Consolas,monospace;white-space:pre-wrap;word-break:break-all;max-height:220px;overflow:auto}
.prev{max-width:100%;max-height:200px;border-radius:10px;margin:8px 0;display:block}.ok{color:var(--mint);font-weight:700}
@media(max-width:760px){.grid{grid-template-columns:1fr}h1{font-size:24px}}
@media(prefers-reduced-motion:reduce){*{transition:none!important;animation:none!important}}
</style></head><body><div class="wrap">
<header><div class="logo"><i></i><i></i></div><div><h1>Kelompok 5</h1></div><div class="stats"><span><b>26</b>mode huruf</span><span><b>256</b>mode byte</span></div></header>
<p class="sub">Enkripsi dan dekripsi teks atau file dengan tujuh cipher klasik. Pilih cipher, isi kunci, lalu jalankan.</p>
<div class="tabs" id="tabs"></div>
<div class="info" id="infoBox"></div>
<div class="bar">
 <div class="seg" id="segMode"><button data-v="encrypt" class="on">Enkripsi</button><button data-v="decrypt">Dekripsi</button></div>
 <div class="seg" id="segType"><button data-v="text" class="on">Teks</button><button data-v="file">File</button></div>
</div>
<section class="keyrow">
 <div id="keybox"><label for="key">Kunci</label><div class="hint" id="khint"></div>
  <div class="kin"><input type="text" id="key" autocomplete="off" oninput="strip()"><button class="btn" onclick="ex()">Isi contoh</button><button class="btn hide" id="genSub" onclick="genSub()">Generate</button></div></div>
 <div id="otpbox" class="hide"><label>File kunci One-Time Pad</label><div class="hint">Berisi huruf acak, minimal sepanjang pesan. Huruf berlebih tidak dipakai.</div>
  <div class="kin"><input type="file" id="keyfile"><input type="text" id="otpn" value="10000" title="Jumlah huruf" style="flex:0 0 110px;min-width:90px"><button class="btn" onclick="genOtp()">Generate OTP (huruf)</button></div></div>
 <div class="strip" id="strip"></div>
</section>
<div class="grid">
 <div class="pane"><div class="ph"><span id="inTitle">Plainteks</span><small id="cnt"></small></div>
  <textarea id="text" placeholder="Ketik atau tempel pesan di sini" oninput="cnt()"></textarea>
  <label class="drop hide" id="drop"><input type="file" id="file"><div style="font-size:30px">&#128196;</div>
   <div id="dtxt">Tarik file ke sini atau klik untuk memilih.<br>Semua jenis file bisa diproses.</div></label></div>
 <div class="pane out"><div class="ph"><span id="outTitle">Cipherteks</span>
  <select id="group" title="Tampilan cipherteks"><option value="0">Tanpa spasi</option><option value="5">Kelompok 5 huruf</option></select></div>
  <div class="res empty" id="out">Hasil akan muncul di sini.</div>
  <div class="acts" id="oacts"><button class="btn" onclick="copyO()">Copy</button><button class="btn" onclick="saveO()">Simpan File</button><button class="btn" onclick="swap()">Pakai sebagai input</button></div></div>
</div>
<div class="cta"><button class="btn go" id="go" onclick="run()">Enkripsi</button></div>
</div><div id="toast"></div>
<script>
const C=[
{id:"shift",n:"Shift",d:"Geser huruf",h:"Satu bilangan bulat k. Contoh: 3",ex:"3"},
{id:"substitution",n:"Substitution",d:"Tukar 26 huruf",h:"Kata kunci atau 26 huruf permutasi. Huruf sisa disusun berurutan.",ex:"QWERTYUIOPASDFGHJKLZXCVBNM"},
{id:"affine",n:"Affine",d:"C = aP + b",h:"Dua bilangan a,b dengan a relatif prima terhadap 26. Contoh: 5,8",ex:"5,8"},
{id:"vigenere",n:"Vigenere",d:"Kunci berulang",h:"Kata kunci bebas panjang, hanya huruf yang dipakai.",ex:"SECRET"},
{id:"hill",n:"Hill",d:"Matriks n x n",h:"n*n bilangan atau huruf. Matriks harus punya balikan. Contoh 3x3: GYBNQKURP",ex:"GYBNQKURP"},
{id:"permutation",n:"Permutation",d:"Acak posisi",h:"Urutan angka (3 1 4 2) atau kata kunci (ZEBRA).",ex:"3 1 4 2"},
{id:"otp",n:"One-Time Pad",d:"Kunci sekali pakai",h:"",ex:""}];
const S={c:"shift",m:"encrypt",t:"text",last:""};const $=i=>document.getElementById(i);
const tabs=$("tabs");C.forEach(c=>{const b=document.createElement("button");b.className="tab";b.dataset.id=c.id;
b.innerHTML="<b>"+c.n+"</b><span>"+c.d+"</span>";b.onclick=()=>{S.c=c.id;ui()};tabs.appendChild(b)});
function seg(id,key){$(id).onclick=e=>{if(e.target.dataset.v){S[key]=e.target.dataset.v;ui()}}}seg("segMode","m");seg("segType","t");
function cur(){return C.find(c=>c.id==S.c)}
function ui(){const c=cur(),enc=S.m=="encrypt",f=S.t=="file";
document.querySelectorAll(".tab").forEach(b=>b.classList.toggle("on",b.dataset.id==S.c));
document.querySelectorAll("#segMode button").forEach(b=>b.classList.toggle("on",b.dataset.v==S.m));
document.querySelectorAll("#segType button").forEach(b=>b.classList.toggle("on",b.dataset.v==S.t));
$("khint").textContent=c.h+(f&&S.c!="otp"?" (Mode file memakai 256 nilai byte.)":"");
$("keybox").classList.toggle("hide",S.c=="otp");$("otpbox").classList.toggle("hide",S.c!="otp");
$("text").classList.toggle("hide",f);$("drop").classList.toggle("hide",!f);$("cnt").classList.toggle("hide",f);
$("inTitle").textContent=f?(enc?"File asli":"File terenkripsi (.dat)"):(enc?"Plainteks":"Cipherteks");
$("outTitle").textContent=f?"Hasil file":(enc?"Cipherteks":"Plainteks");
$("group").classList.toggle("hide",!(enc&&!f));$("oacts").classList.toggle("hide",f);
$("go").textContent=enc?"Enkripsi":"Dekripsi";strip();cnt();showInfo()}
function ex(){$("key").value=cur().ex;strip()}
function cnt(){const n=($("text").value.match(/[a-zA-Z]/g)||[]).length;$("cnt").textContent=n+" huruf diproses (angka dan simbol diabaikan)"}
function gcd(a,b){return b?gcd(b,a%b):Math.abs(a)}
function strip(){const el=$("strip"),k=$("key").value,c=S.c;let enc=null;
if(S.t=="text"){if(c=="shift"){const m=k.match(/-?\d+/);if(m){const s=+m[0];enc=i=>(((i+s)%26)+26)%26}}
else if(c=="affine"){const n=k.match(/-?\d+/g);if(n&&n.length>1&&gcd(+n[0],26)==1){const a=+n[0],b=+n[1];enc=i=>(((a*i+b)%26)+26)%26}}
else if(c=="substitution"){const l=(k.toUpperCase().match(/[A-Z]/g)||[]).map(x=>x.charCodeAt(0)-65);
if(l.length){const seen=[];l.concat([...Array(26).keys()]).forEach(x=>{if(!seen.includes(x))seen.push(x)});enc=i=>seen[i]}}}
if(!enc){el.classList.add("hide");return}el.classList.remove("hide");
const L=i=>String.fromCharCode(65+i),e=[...Array(26).keys()].map(enc),dec=S.m=="decrypt";
let top=[...Array(26).keys()],bot=e;if(dec){bot=Array(26);e.forEach((v,i)=>bot[v]=i)}
el.innerHTML="<table><tr><th>"+(dec?"Cipher":"Plain")+"</th>"+top.map(i=>"<td>"+L(i)+"</td>").join("")+"</tr><tr><th>"+(dec?"Plain":"Cipher")+"</th>"+bot.map(i=>"<td>"+L(i)+"</td>").join("")+"</tr></table>"}
function toast(t,bad){const o=$("toast");o.textContent=t;o.className="show"+(bad?" bad":"");clearTimeout(o.t);o.t=setTimeout(()=>o.className="",3200)}
const FORM={shift:"C = (P + k) mod 26",substitution:"C = pi(P)  |  P = pi^-1(C)",affine:"C = (a*P + b) mod 26",vigenere:"Ci = (Pi + K[i mod m]) mod 26",hill:"C = K * P  (mod 26)",permutation:"C = blok P diacak oleh urutan kunci",otp:"Ci = (Pi + Ki) mod 26"};
const NOTE=["Plainteks dan cipherteks ditampilkan di layar.","Cipherteks bisa tanpa spasi atau kelompok 5 huruf.","Kunci dimasukkan pengguna, panjang bebas.","File apa pun dienkripsi per byte, lalu bisa didekripsi kembali ke file asli."];
function esc(s){return String(s).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]))}
function pair(l1,a,l2,b){return '<div class="lb">'+l1+'</div><pre class="term">'+esc(a)+'</pre><div class="lb">'+l2+'</div><pre class="term">'+esc(b)+'</pre>'}
function showInfo(){const c=cur(),f=S.t=="file";
$("infoBox").innerHTML='<div><b>'+c.n+' Cipher</b><code>'+FORM[c.id].replace(/mod 26/,f?"mod 256":"mod 26")+'</code></div><ul>'+NOTE.map(n=>'<li>'+n+'</li>').join("")+'</ul>';
$("genSub").classList.toggle("hide",S.c!="substitution");$("genSub").textContent=f?"Generate substitution byte key":"Generate kunci 26 huruf";
if(f&&S.c=="substitution")$("khint").textContent+=" Mode file: 256 angka permutasi 0-255 (tombol Generate) atau kata kunci sebagai seed."}
function genSub(){const f=S.t=="file",n=f?256:26,a=[...Array(n).keys()];
for(let i=n-1;i>0;i--){const j=crypto.getRandomValues(new Uint32Array(1))[0]%(i+1);[a[i],a[j]]=[a[j],a[i]]}
$("key").value=f?a.join(" "):a.map(x=>String.fromCharCode(65+x)).join("");strip();toast("Kunci acak dibuat. Simpan kunci ini untuk dekripsi.")}
function genOtp(){const n=Math.max(1,parseInt($("otpn").value)||10000);location="/genkey?n="+n}
function dl(){const a=document.createElement("a");a.href=S.url;a.download=S.fname;a.click()}
async function run(){const fd=new FormData(),btn=$("go"),lab=btn.textContent,enc=S.m=="encrypt";
fd.append("mode",S.m);fd.append("cipher",S.c);fd.append("input_type",S.t);fd.append("key",$("key").value);
fd.append("text",$("text").value);fd.append("group",$("group").value);
if($("file").files[0])fd.append("file",$("file").files[0]);if($("keyfile").files[0])fd.append("keyfile",$("keyfile").files[0]);
btn.disabled=true;btn.innerHTML='<span class="spin"></span>Memproses';
try{const r=await fetch("/process",{method:"POST",body:fd});
if(!r.ok){const j=await r.json();toast(j.error,true);return}
if(S.t=="file"){const b=await r.blob(),n=decodeURIComponent(r.headers.get("X-Filename")),src=$("file").files[0];
if(S.url)URL.revokeObjectURL(S.url);S.blob=b;S.fname=n;S.url=URL.createObjectURL(b);
const img=!enc&&/\.(png|jpe?g|gif|webp|bmp)$/i.test(n);
$("out").className="res";$("out").innerHTML='<div class="ok">'+(enc?"Enkripsi":"Dekripsi")+' berhasil</div><div class="lb">'+esc(n)+'<br>'+(src?(src.size/1024).toFixed(1):"?")+' KB menjadi '+(b.size/1024).toFixed(1)+' KB</div>'+(img?'<img class="prev" src="'+S.url+'">':'')+'<button class="btn" onclick="dl()">Simpan File</button>';
toast("File berhasil diproses");return}
const j=await r.json();S.last=j.output;$("out").className="res";
$("out").innerHTML=enc?pair("Plainteks (huruf saja)",j.input,"Cipherteks",j.output):pair("Cipherteks",j.input,"Plainteks",j.output)}
catch(e){toast("Gagal terhubung ke server",true)}finally{btn.disabled=false;btn.textContent=lab}}
function copyO(){if(!S.last)return toast("Belum ada hasil",true);navigator.clipboard.writeText(S.last).then(()=>toast("Hasil disalin"))}
function saveO(){if(!S.last)return toast("Belum ada hasil",true);const a=document.createElement("a");
a.href=URL.createObjectURL(new Blob([S.last],{type:"text/plain"}));a.download=(S.m=="encrypt"?"cipherteks":"plainteks")+".txt";a.click()}
function swap(){if(!S.last)return toast("Belum ada hasil",true);$("text").value=S.last;S.m=S.m=="encrypt"?"decrypt":"encrypt";S.last="";
$("out").className="res empty";$("out").textContent="Hasil akan muncul di sini.";ui();toast("Hasil dipindah ke kolom input")}
const d=$("drop"),fi=$("file");fi.onchange=()=>{const f=fi.files[0];if(!f)return;$("dtxt").innerHTML="<b>"+esc(f.name)+"</b><br>"+(f.size/1024).toFixed(1)+" KB"+(f.type.startsWith("image/")?'<img class="prev" src="'+URL.createObjectURL(f)+'">':"")};
["dragover","dragenter"].forEach(e=>d.addEventListener(e,x=>{x.preventDefault();d.classList.add("over")}));
["dragleave","drop"].forEach(e=>d.addEventListener(e,x=>{x.preventDefault();d.classList.remove("over")}));
d.addEventListener("drop",x=>{if(x.dataTransfer.files.length){fi.files=x.dataTransfer.files;fi.onchange()}});
ui();
</script></body></html>
"""

if __name__ == "__main__":
    app.run(debug=True)
