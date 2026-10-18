require('dns').setDefaultResultOrder('ipv4first'); // prefere IPv4 (o Render não alcança endereços só IPv6)
const http=require('http'),fs=require('fs'),path=require('path'),{WebSocketServer}=require('ws');
const RK=['A','2','3','4','5','6','7','8','9','10','J','Q','K'],SU='♠♥♦♣';
const name=c=>c.j?'Coringa':RK[c.r]+SU[c.s];
// ---------- configuração das apostas (valores em R$ inteiros; saldo é só contabilidade, não movimenta dinheiro real) ----------
const CFG={entry:10,maxCall:210,minCall:10,minDeposit:10,maxDeposit:1000,chips:[10,30,50,100,210], // valores das fichas (a chamada é uma ficha escolhida)
  maxPlayers:11,
  botAccepts:true,   // bots aceitam chamadas (false = bots sempre desistem)
  callerPays:true};  // quem chama também coloca o valor da chamada no pote (se alguém aceitar)

// ---------- regras ----------
function isGroup(cs){
  const n=cs.length;if(n<3)return false;
  const nj=cs.filter(c=>c.j).length,rg=cs.filter(c=>!c.j);
  if(nj>1||rg.length<2)return false;
  if(n<=4&&rg.every(c=>c.r==rg[0].r)&&new Set(rg.map(c=>c.s)).size==rg.length)return true;
  if(!rg.every(c=>c.s==rg[0].s)||new Set(rg.map(c=>c.r)).size!=rg.length)return false;
  const t=hi=>{const v=rg.map(c=>c.r==0&&hi?13:c.r),mn=Math.min(...v),mx=Math.max(...v);return mx-mn+1<=n&&Math.max(mx-n+1,0)<=Math.min(mn,14-n)};
  return t(0)||t(1);
}
function covered(h){
  const n=h.length,memo=new Map();
  const f=m=>{
    if(!m)return 0;if(memo.has(m))return memo.get(m);
    const b=m&-m,rest=m^b;let r=f(rest);
    for(let s=rest;s;s=(s-1)&rest){
      const g=b|s,cs=[];for(let i=0;i<n;i++)if(g>>i&1)cs.push(h[i]);
      if(cs.length>=3&&isGroup(cs))r=Math.max(r,cs.length+f(m^g));
    }
    memo.set(m,r);return r;
  };
  return f((1<<n)-1);
}
function part(h){
  if(!h.length)return[];
  const n=h.length;
  for(let s=0;s<1<<(n-1);s++){
    const g=[h[0]],rest=[];
    for(let i=1;i<n;i++)(s>>(i-1)&1?g:rest).push(h[i]);
    if(isGroup(g)){const p=part(rest);if(p)return[g,...p]}
  }
  return null;
}
function near(h){
  let s=0;
  for(let i=0;i<h.length;i++)for(let j=i+1;j<h.length;j++){
    const a=h[i],b=h[j];
    if(a.j||b.j)s+=2;
    else if(a.r==b.r&&a.s!=b.s)s+=3;
    else if(a.s==b.s&&a.r!=b.r&&(Math.abs(a.r-b.r)<=2||(a.r==0&&b.r>=11)||(b.r==0&&a.r>=11)))s+=3;
  }
  return s;
}
const score=h=>covered(h)*100+near(h);
function bestDiscard(h){
  let b=null;
  h.forEach((c,i)=>{
    const h9=h.filter((_,x)=>x!=i),cv=covered(h9),sc=cv*100+near(h9);
    if(!b||sc>b.sc)b={i,sc,cv,win:cv==h9.length};
  });
  return b;
}

// ---------- salas ----------
const rooms={};
const auto=p=>p.bot||!p.ws;
const topCard=R=>R.disc[R.disc.length-1];

const payers=R=>R.players.filter((p,i)=>p.st=='in'&&(CFG.callerPays||i!=R.call.by));
const calls=R=>R.call&&R.players.filter(p=>p.st=='in').length>1?R.call.amt*payers(R).length:0;
const nextIn=(R,i)=>{let t=i;do{t=(t+1)%R.players.length}while(R.players[t].st!='in');return t};
function finish(R,w,how){ // registra a rodada no histórico e credita o prêmio (só aqui, uma vez)
  const P=R.players,c=calls(R)||0,pr=w==null?0:R.pot0+c;
  if(w!=null)P[w].bal+=pr;
  Object.assign(R.cur,{in:P.filter(p=>p.st=='in').map(p=>p.n),fold:P.filter(p=>p.st=='f').map(p=>p.n),
    call:R.call?{by:P[R.call.by].n,amt:R.call.amt}:null,pot0:R.pot0,calls:c,prize:pr,winner:w==null?null:P[w].n,how});
  R.hist.push(R.cur);if(R.hist.length>20)R.hist.shift();
}
function startPlay(R){
  const a=R.players.map((p,i)=>p.st=='in'?i:-1).filter(i=>i>=0);
  R.turn=a[Math.random()*a.length|0];R.stage='play';R.phase='draw';
  R.msg=`Disputa com ${a.length} jogadores (chamada de R$ ${R.call.amt}). ${R.players[R.turn].n} começa.`;
  loop(R);
}
function betCheck(R){
  const P=R.players;
  P.forEach(p=>{ // jogadores offline desistem; bots seguem CFG
    if(p.st!='u'||!auto(p))return;
    if(!p.bot)p.st='f';
    else if(R.call)p.st=CFG.botAccepts?'in':'f';
    else if(!P.some(x=>!x.bot&&x.st=='u'))p.st='f';
  });
  if(P.some(p=>p.st=='u'))return send(R);
  if(!R.call){
    finish(R,null,'sem vencedor');R.carry=R.pot0;R.started=false;R.stage='idle';
    R.msg=`Todos desistiram sem chamada. Os R$ ${R.pot0} do pote acumulam para a próxima rodada.`;
    return send(R);
  }
  if(P.filter(p=>p.st=='in').length<2){
    const w=R.call.by;R.win=w;R.fw=true;R.stage='end';finish(R,w,'todos desistiram');
    R.msg=`🏆 ${P[w].n} venceu: ninguém aceitou a chamada. Prêmio: R$ ${R.cur.prize} (só o pote inicial).`;
    return send(R);
  }
  if(!R.charged){R.charged=true;payers(R).forEach(p=>p.bal-=R.call.amt)} // cobrança única
  startPlay(R);
}
function bet(R,i,m){
  const p=R.players[i];
  if(m.t=='fold'){p.st='f';R.msg=`${p.n} desistiu desta mão.`}
  else if(m.t=='accept'){if(!R.call)return;if(p.bal<R.call.amt)return note(p,'Saldo insuficiente para aceitar. Você pode desistir desta mão.');p.st='in';R.msg=`${p.n} aceitou a chamada.`}
  else{
    const amt=Math.floor(+m.amt);
    if(R.call||!CFG.chips.includes(amt))return;if(p.bal<amt)return note(p,'Saldo insuficiente para essa ficha.');
    R.call={by:i,amt};p.st='in';R.msg=`${p.n} chamou R$ ${amt}. Aceitar ou desistir?`;
  }
  betCheck(R);
}
function deal(R){
  const d=[];
  for(let k=0;k<2;k++)for(let s=0;s<4;s++)for(let r=0;r<13;r++)d.push({r,s,id:d.length});
  for(let i=0;i<4;i++)d.push({j:1,id:d.length});
  for(let i=d.length-1;i>0;i--){const j=Math.random()*(i+1)|0;[d[i],d[j]]=[d[j],d[i]]}
  R.players.forEach(p=>p.h=d.splice(0,9));
  R.stock=d;R.disc=[d.pop()];R.turn=-1;
  R.phase='draw';R.win=-1;R.started=true;R.fw=false;R.charged=false;R.call=null;R.stage='bet';
  R.pot0=CFG.entry*R.players.length+R.carry;R.carry=0; // entrada obrigatória de todos (+ pote acumulado, se houve)
  R.players.forEach(p=>{p.bal=(p.bal||0)-CFG.entry;p.st='u'});R.cur={r:++R.rn};
  R.msg=`Nova rodada: entrada de R$ ${CFG.entry} cobrada de todos. Chame, aceite ou desista.`;
  betCheck(R);
}
function draw(R,src){
  const p=R.players[R.turn];
  if(src=='stock'&&!R.stock.length&&R.disc.length>1){
    const top=R.disc.pop();R.stock=R.disc.sort(()=>Math.random()-.5);R.disc=[top];
  }
  if(!R.stock.length)src='disc';
  const c=src=='stock'?R.stock.pop():R.disc.pop();
  p.h.push(c);R.phase='discard';
  R.msg=`${p.n} ${src=='stock'?'comprou do monte':'pegou '+name(c)+' do descarte'}.`;
}
function discard(R,id){
  const p=R.players[R.turn],i=p.h.findIndex(c=>c.id==id);
  if(i<0)return;
  const c=p.h.splice(i,1)[0];R.disc.push(c);
  if(covered(p.h)==9){R.win=R.turn;finish(R,R.win,'bateu');R.msg=`🏆 ${p.n} bateu descartando ${name(c)} e leva R$ ${R.cur.prize}!`;return send(R)}
  R.msg=`${p.n} descartou ${name(c)}.`;
  R.turn=nextIn(R,R.turn);R.phase='draw';loop(R);
}
function step(R){
  const p=R.players[R.turn];
  if(R.win>=0||!R.started||R.stage!='play'||!auto(p))return;
  if(R.phase=='draw'){
    const bd=bestDiscard(p.h.concat([topCard(R)]));
    draw(R,bd.win||bd.sc>score(p.h)?'disc':'stock');
    send(R);setTimeout(()=>step(R),900);
  }else{const b=bestDiscard(p.h);discard(R,p.h[b.i].id)}
}
function loop(R){
  send(R);
  if(R.win>=0||R.stage!='play')return;
  const p=R.players[R.turn];
  if(auto(p))setTimeout(()=>step(R),p.bot?900:8000); // humano offline: joga o bot após 8s
}
function hint(R,i){
  if(!R.started||R.win>=0)return '';
  const me=R.players[i],h=me.h;
  if(R.turn!=i)return `Cartas suas em jogos agora: <b>${covered(h)} de 9</b>.`;
  if(R.phase=='draw'){
    const top=topCard(R),bd=bestDiscard(h.concat([top])),cur=score(h);
    return `Cartas em jogos: <b>${covered(h)} de 9</b>. O descarte (${name(top)}) `+(bd.win?'<b>permite bater agora!</b>':bd.sc>cur?'<b>melhora</b> sua mão: vale pegar.':'não melhora sua mão: prefira o monte.');
  }
  const b=bestDiscard(h);
  return b.win?`Descartando <b>${name(h[b.i])}</b> você bate!`:`Sugestão: descartar <b>${name(h[b.i])}</b>. Ficaria com <b>${b.cv} de 9</b> cartas em jogos.`;
}
function view(R,i){
  const study=R.players.every((p,k)=>k==i||p.bot); // modo estudo só em treino: todos os outros jogadores são bots
  return{t:'state',code:R.code,started:R.started,me:i,
    players:R.players.map(p=>({n:p.n,bot:!!p.bot,off:!p.bot&&!p.ws,c:p.h?p.h.length:0,st:p.st||'',bal:p.bal||0})),
    hand:R.players[i].h||[],top:R.disc&&topCard(R),stock:R.stock?R.stock.length:0,
    turn:R.turn,phase:R.phase,win:R.win,msg:R.msg,study:study,hint:study?hint(R,i):'',
    melds:R.win>=0&&!R.fw?part(R.players[R.win].h):null,
    stage:R.stage||'',call:R.call||null,ent:CFG.entry,min:CFG.minCall,max:CFG.maxCall,chips:CFG.chips,dep:{on:GATE.on,min:CFG.minDeposit,max:CFG.maxDeposit},mp:CFG.maxPlayers,
    pot0:R.pot0||0,calls:calls(R)||0,carry:R.carry||0,hist:R.hist.slice(-8)};
}
function send(R){
  pushRooms();
  R.players.forEach((p,i)=>{if(p.ws&&p.ws.readyState==1)p.ws.send(JSON.stringify(view(R,i)))});
}

// ---------- servidor ----------
// ---------- carteiras (saldo) ----------
const crypto=require('crypto'),ADMIN_KEY=process.env.ADMIN_KEY||'';
const DB_FILE=process.env.DATA_FILE||path.join(__dirname,'data.json');
let DB={wallets:{},log:[],deps:{}},dbT=null,pool=null;
if(process.env.DATABASE_URL){ // com DATABASE_URL (Postgres) o saldo sobrevive a reinícios; sem ela usa arquivo local
  const {Pool}=require('pg'),u=process.env.DATABASE_URL;
  pool=new Pool({connectionString:u,max:3,connectionTimeoutMillis:10000,ssl:/localhost|127\.0\.0\.1/.test(u)?false:{rejectUnauthorized:false}});
}
async function loadDB(){
  if(pool){
    await pool.query('create table if not exists kv(k text primary key,v text not null)');
    await pool.query('alter table kv enable row level security').catch(()=>{}); // impede leitura pela API pública do Supabase
    const r=await pool.query("select v from kv where k='db'");if(r.rows[0])DB=JSON.parse(r.rows[0].v);
  }else try{DB=JSON.parse(fs.readFileSync(DB_FILE,'utf8'))}catch{}
  DB.wallets=DB.wallets||{};DB.log=DB.log||[];DB.deps=DB.deps||{};
}
async function flush(){
  clearTimeout(dbT);const t=JSON.stringify(DB);
  if(pool)await pool.query("insert into kv(k,v) values('db',$1) on conflict(k) do update set v=excluded.v",[t]);
  else{fs.writeFileSync(DB_FILE+'.tmp',t);fs.renameSync(DB_FILE+'.tmp',DB_FILE)}
}
const save=()=>{clearTimeout(dbT);dbT=setTimeout(()=>flush().catch(e=>console.error('Erro ao salvar:',e.message)),300)};
process.on('uncaughtException',e=>console.error('Erro não tratado:',e));process.on('unhandledRejection',e=>console.error('Promessa rejeitada:',e));
process.on('SIGTERM',()=>flush().catch(()=>{}).finally(()=>process.exit(0)));
const hp=(pin,salt=crypto.randomBytes(8).toString('hex'))=>salt+':'+crypto.scryptSync(pin,salt,32).toString('hex');
function auth(name,pin){ // nome + PIN = carteira; primeiro acesso define o PIN
  const key=name.toLowerCase();let w=DB.wallets[key];
  if(w&&w.until>Date.now())return 'Muitas tentativas erradas. Aguarde 1 minuto.';
  if(!w)w=DB.wallets[key]={n:name,pin:null,bal:0};
  if(!w.pin){w.pin=hp(pin);save();return w}
  const[s,h]=w.pin.split(':');
  if(crypto.timingSafeEqual(Buffer.from(h,'hex'),crypto.scryptSync(pin,s,32))){w.fail=0;return w}
  w.fail=(w.fail||0)+1;if(w.fail>=5){w.until=Date.now()+60000;w.fail=0}save();
  return 'PIN incorreto para esse nome.';
}
// ---------- depósito por Pix (SigiloPay) ----------
const E=process.env,GATE={base:E.SIGILO_BASE||'https://app.sigilopay.com.br/api/v1',pub:E.SIGILO_PUBLIC_KEY||'',sec:E.SIGILO_SECRET_KEY||'',
  url:(E.PUBLIC_URL||'').replace(/\/$/,''),wsec:E.WEBHOOK_SECRET||'',tok:E.SIGILO_WEBHOOK_TOKEN||''};
GATE.on=!!(GATE.pub&&GATE.sec&&GATE.url&&GATE.wsec);
const QRCode=require('qrcode'),r2=v=>Math.round(v*100)/100;
function strings(o,d=0,out=[]){if(d>7||o==null)return out;if(typeof o=='string')out.push(o);else if(typeof o=='object')for(const k in o)strings(o[k],d+1,out);return out}
async function createPix(amount,identifier){
  const r=await fetch(GATE.base+'/gateway/pix/deposit',{method:'POST',signal:AbortSignal.timeout(15000),
    headers:{'Content-Type':'application/json','x-public-key':GATE.pub,'x-secret-key':GATE.sec},
    body:JSON.stringify({amount,identifier,callbackUrl:GATE.url+'/webhook/sigilopay?s='+encodeURIComponent(GATE.wsec)})});
  const j=await r.json().catch(()=>({}));
  if(!r.ok){console.error('SigiloPay',r.status,JSON.stringify(j).slice(0,500));throw new Error(j.message||'Gateway respondeu '+r.status)}
  return j;
}
async function deposit(p,ws,m){
  if(!GATE.on)return note(p,'Depósito por Pix ainda não está ativo. Peça saldo ao administrador.');
  const amt=r2(+m.amount),key=p.wal.n.toLowerCase();
  if(!(amt>=CFG.minDeposit&&amt<=CFG.maxDeposit))return note(p,`Informe um valor entre R$ ${CFG.minDeposit} e R$ ${CFG.maxDeposit}.`);
  if(Object.values(DB.deps).filter(d=>d.w==key&&d.st=='PENDING'&&Date.now()-d.at<3600e3).length>=3)return note(p,'Você já tem 3 Pix pendentes. Pague um deles ou aguarde 1 hora.');
  const id=crypto.randomUUID();
  try{
    const j=await createPix(amt,id);
    const code=strings(j).filter(x=>x.startsWith('000201')).sort((a,b)=>b.length-a.length)[0];
    if(!code){console.error('Resposta sem código Pix:',JSON.stringify(j).slice(0,500));throw new Error('Resposta inesperada do gateway.')}
    DB.deps[id]={w:key,amt,tid:String(j.transactionId||''),st:'PENDING',at:Date.now()};save();
    rawSend(ws,{t:'pix',amount:amt,code,img:await QRCode.toDataURL(code,{margin:1,width:280})});
  }catch(e){console.error('Pix:',e.message);note(p,'Não foi possível gerar o Pix agora: '+e.message)}
}
function tellWallet(w,text,paid){
  Object.values(rooms).forEach(R=>{const ps=R.players.filter(p=>p.wal===w);if(!ps.length)return;
    ps.forEach(p=>paid&&p.ws&&rawSend(p.ws,{t:'paid',amt:paid}));sysMsg(R,text);send(R)});
}
function onHook(m){
  if(GATE.tok&&m.token!==GATE.tok)return console.error('Webhook com token inválido');
  const ev=String(m.event||''),ids=new Set(strings(m));
  const id=Object.keys(DB.deps).find(k=>ids.has(k)||(DB.deps[k].tid&&ids.has(DB.deps[k].tid)));
  if(!id)return console.log('Webhook sem depósito correspondente:',ev);
  const d=DB.deps[id],w=DB.wallets[d.w];
  if(ev=='TRANSACTION_PAID'){
    if(d.st=='PAID'||d.st=='REFUNDED'||d.st=='CHARGED_BACK')return; // crédito único
    d.st='PAID';d.paidAt=Date.now();w.bal=r2(w.bal+d.amt);
    DB.log.push({at:Date.now(),n:w.n,d:d.amt,bal:w.bal,note:'Depósito Pix '+d.tid});if(DB.log.length>500)DB.log.shift();
    flush().catch(e=>console.error('Erro ao salvar:',e.message));
    tellWallet(w,`${w.n} adicionou saldo via Pix: +R$ ${d.amt}.`,d.amt);
  }else if(ev=='TRANSACTION_CANCELED'){if(d.st=='PENDING'){d.st='CANCELED';save()}}
  else if(ev=='TRANSACTION_REFUNDED'||ev=='TRANSACTION_CHARGED_BACK'){
    d.st=ev=='TRANSACTION_REFUNDED'?'REFUNDED':'CHARGED_BACK';
    DB.log.push({at:Date.now(),n:w.n,d:0,bal:w.bal,note:`ATENÇÃO: ${d.st} no Pix de R$ ${d.amt} (${d.tid}). Revise o saldo.`});save();
  }
}
function webhook(q,r){
  const s=new URL(q.url,'http://x').searchParams.get('s')||'';
  if(!GATE.wsec||s.length!=GATE.wsec.length||!crypto.timingSafeEqual(Buffer.from(s),Buffer.from(GATE.wsec))){r.writeHead(401);return r.end()}
  let b='';q.on('data',d=>{b+=d;if(b.length>2e5)q.destroy()});
  q.on('end',()=>{r.writeHead(200);r.end('ok');let m;try{m=JSON.parse(b)}catch{return}try{onHook(m)}catch(e){console.error('Webhook:',e)}});
}
function adminHandler(q,r){
  const J=(c,o)=>{r.writeHead(c,{'Content-Type':'application/json'});r.end(JSON.stringify(o))};
  if(!ADMIN_KEY){r.writeHead(404);return r.end('Admin desativado: defina a variável ADMIN_KEY no servidor.')}
  const u=q.url.split('?')[0];
  if(q.method=='GET'&&(u=='/admin'||u=='/admin/')){r.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});return r.end(adminHtml)}
  const k=String(q.headers['x-admin-key']||'');
  const ok=k.length==ADMIN_KEY.length&&crypto.timingSafeEqual(Buffer.from(k),Buffer.from(ADMIN_KEY));
  if(!ok)return setTimeout(()=>J(401,{e:'Chave incorreta.'}),600);
  if(q.method=='GET'&&u=='/admin/api/state')return J(200,{wallets:Object.values(DB.wallets).map(w=>({n:w.n,bal:w.bal,pin:!!w.pin})).sort((a,b)=>a.n.localeCompare(b.n)),log:DB.log.slice(-40),deps:Object.values(DB.deps).map(d=>({n:(DB.wallets[d.w]||{}).n,amt:d.amt,st:d.st,at:d.at})).sort((a,b)=>b.at-a.at).slice(0,30)});
  if(q.method!='POST')return J(404,{e:'Não encontrado.'});
  let b='';q.on('data',d=>{b+=d;if(b.length>5000)q.destroy()});
  q.on('end',()=>{
    let m;try{m=JSON.parse(b)}catch{return J(400,{e:'Pedido inválido.'})}
    const name=clean(m.name,12),key=name.toLowerCase();
    if(!name)return J(400,{e:'Informe o nome do jogador.'});
    if(u=='/admin/api/resetpin'){const w=DB.wallets[key];if(!w)return J(404,{e:'Carteira não encontrada.'});w.pin=null;w.fail=0;w.until=0;save();return J(200,{ok:1})}
    if(u=='/admin/api/credit'){
      const amt=Math.round(+m.amount*100)/100;
      if(!isFinite(amt)||amt==0||Math.abs(amt)>100000)return J(400,{e:'Valor inválido.'});
      const w=DB.wallets[key]||(DB.wallets[key]={n:name,pin:null,bal:0});
      if(w.bal+amt<0)return J(400,{e:`Saldo insuficiente: ${w.n} tem R$ ${w.bal}.`});
      w.bal=Math.round((w.bal+amt)*100)/100;
      DB.log.push({at:Date.now(),n:w.n,d:amt,bal:w.bal,note:clean(m.note,80)});if(DB.log.length>500)DB.log.shift();save();
      Object.values(rooms).forEach(R=>{if(R.players.some(p=>p.wal===w)){sysMsg(R,`${w.n}: saldo ${amt>0?'adicionado':'ajustado'} (${amt>0?'+':''}R$ ${amt}).`);send(R)}});
      return J(200,{n:w.n,bal:w.bal});
    }
    J(404,{e:'Não encontrado.'});
  });
}
const html=fs.readFileSync(path.join(__dirname,'index.html'));
let adminHtml='';try{adminHtml=fs.readFileSync(path.join(__dirname,'admin.html'))}catch{}
const server=http.createServer((q,r)=>{
  if(q.url=='/health'){r.writeHead(200,{'Content-Type':'application/json'});return r.end(JSON.stringify({ok:1,pix:GATE.on,banco:pool?'postgres':'arquivo',indexComBotaoSaldo:html.includes('id="dp"'),adminAtivo:!!ADMIN_KEY}))}
  if(q.method=='POST'&&q.url.startsWith('/webhook/sigilopay'))return webhook(q,r);
  if(q.url.startsWith('/admin'))return adminHandler(q,r);
  r.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});r.end(html)});
const wss=new WebSocketServer({server});
const clean=(s,n)=>String(s||'').replace(/[<>&"'`]/g,'').trim().slice(0,n);
const rawSend=(ws,o)=>{if(ws.readyState==1)ws.send(JSON.stringify(o))};
const note=(p,m)=>p.ws&&rawSend(p.ws,{t:'note',m});
const err=(ws,m)=>rawSend(ws,{t:'err',m});
const listRooms=()=>Object.values(rooms).map(R=>({code:R.code,lock:!!R.pass,n:R.players.length,mp:CFG.maxPlayers,playing:R.started&&R.win<0}));
let lt=null;
function pushRooms(){clearTimeout(lt);lt=setTimeout(()=>{const l=listRooms();wss.clients.forEach(c=>{if(!c.inRoom)rawSend(c,{t:'rooms',list:l})})},150)}
const cast=(R,o)=>R.players.forEach(p=>p.ws&&rawSend(p.ws,o));
const sysMsg=(R,text)=>{const e={sys:1,n:'',text};R.chat.push(e);if(R.chat.length>60)R.chat.shift();cast(R,{t:'chat',m:e})};

wss.on('connection',ws=>{
  ws.on('error',e=>console.error('WS:',e.message));
  let R=null,me=null;
  rawSend(ws,{t:'rooms',list:listRooms()});
  function leave(){
    if(!R)return;
    if(me.ws&&me.ws!==ws){R=null;me=null;return} // já reconectou em outra aba/conexão
    const r=R,p=me;R=null;me=null;ws.inRoom=false;
    if(!r.started||r.win>=0){
      r.players=r.players.filter(x=>x!==p);
      r.players.sort((a,b)=>!!a.bot-!!b.bot); // anfitrião sempre humano
      if(r.players.some(x=>!x.bot))sysMsg(r,p.n+' saiu da sala.');
      r.started=false;r.win=-1;r.msg='Aguardando jogadores.';
      if(!r.players.some(x=>!x.bot)){delete rooms[r.code];return pushRooms()}
      return send(r);
    }
    p.ws=null; // no meio da partida: vaga fica reservada e o bot joga até voltar
    sysMsg(r,p.n+' desconectou. Um bot joga por ele até voltar.');
    if(r.stage=='bet')betCheck(r);else if(r.players[r.turn]===p)loop(r);else send(r);
    setTimeout(()=>{if(rooms[r.code]===r&&r.players.every(x=>x.bot||!x.ws)){delete rooms[r.code];pushRooms()}},600000);
  }
  ws.on('message',raw=>{
    let m;try{m=JSON.parse(raw)}catch{return}
    if(m.t=='join'){
      if(R)return;
      const code=String(m.room||'').toUpperCase().replace(/[^A-Z0-9_-]/g,'').slice(0,14);
      if(!code)return err(ws,'Informe um nome para a sala.');
      const pin=String(m.pin||'');if(pin.length<4||pin.length>12)return err(ws,'Informe seu PIN (4 a 12 caracteres).');
      const w=auth(clean(m.name,12)||'Jogador',pin);if(typeof w=='string')return err(ws,w);
      let r=rooms[code],fresh=false;
      if(!r){
        if(!m.create)return err(ws,'Essa sala não existe mais.');
        r=rooms[code]={code,pass:clean(m.pass,20),players:[],started:false,win:-1,msg:'Aguardando jogadores.',chat:[],hist:[],rn:0,carry:0,pot0:0};
      }else if(m.create)return err(ws,'Já existe uma sala com esse nome.');
      let p=r.players.find(x=>!x.bot&&x.wal===w);
      if(!p){
        if(r.pass&&clean(m.pass,20)!==r.pass)return err(ws,'Senha incorreta.');
        if(r.started&&r.win<0)return err(ws,'Partida em andamento nessa sala.');
        if(r.players.length>=CFG.maxPlayers)return err(ws,`Mesa cheia (${CFG.maxPlayers} lugares).`);
        p={n:w.n,tok:m.tok,ws,wal:w};Object.defineProperty(p,'bal',{get:()=>w.bal,set:v=>{w.bal=Math.round(v*100)/100;save()}});r.players.push(p);fresh=true;
      }else{if(p.ws&&p.ws!==ws)p.ws.close();p.ws=ws}
      R=r;me=p;ws.inRoom=true;
      rawSend(ws,{t:'chatlog',log:r.chat});
      if(fresh)sysMsg(r,p.n+' entrou na sala.');
      if(r.started&&r.win<0&&r.players[r.turn]===p)return loop(r);
      return send(r);
    }
    if(!R||!me)return;
    if(m.t=='deposit')return deposit(me,ws,m);
    if(m.t=='leave'){leave();rawSend(ws,{t:'left'});return rawSend(ws,{t:'rooms',list:listRooms()})}
    if(m.t=='chat'){
      const text=String(m.text||'').trim().slice(0,200);if(!text)return;
      const e={n:me.n,text};R.chat.push(e);if(R.chat.length>60)R.chat.shift();
      return cast(R,{t:'chat',m:e});
    }
    const i=R.players.indexOf(me),host=i==0,over=!R.started||R.win>=0;
    if(m.t=='bot'&&host&&over&&R.players.length<CFG.maxPlayers){
      const k=R.players.filter(p=>p.bot).length+1;
      R.players.push({n:'Bot '+k,bot:1});R.started=false;R.win=-1;R.msg='Aguardando jogadores.';send(R);
    }else if(m.t=='start'&&host&&over&&R.players.length>=2){
      const poor=R.players.filter(p=>!p.bot&&p.bal<CFG.entry).map(p=>p.n);
      if(poor.length)sysMsg(R,`Sem saldo para a entrada de R$ ${CFG.entry}: ${poor.join(', ')}. Peça ao administrador para adicionar saldo.`);
      else deal(R);
    }
    else if(R.stage=='bet'&&R.started&&R.win<0&&me.st=='u'&&['fold','call','accept'].includes(m.t))bet(R,i,m);
    else if(R.started&&R.win<0&&R.turn==i){
      if(m.t=='draw'&&R.phase=='draw'){draw(R,m.src=='disc'?'disc':'stock');send(R)}
      else if(m.t=='discard'&&R.phase=='discard')discard(R,m.id);
    }
  });
  ws.on('close',leave);
});
setInterval(()=>wss.clients.forEach(c=>c.ping()),25000);
const PORT=process.env.PORT||3000;
loadDB().then(()=>server.listen(PORT,()=>console.log('Pife online em http://localhost:'+PORT+(GATE.on?' (Pix ativo)':' (Pix desativado)')+(pool?' [Postgres]':' [arquivo local]')))).catch(e=>{console.error('Falha ao iniciar (confira a DATABASE_URL):',e.code||'',e.message,'| servidor do banco na URL:',((process.env.DATABASE_URL||'').match(/@([^/:?]+)/)||[])[1]||'(URL sem endereço)');process.exit(1)});
