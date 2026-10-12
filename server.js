const http=require('http'),fs=require('fs'),path=require('path'),{WebSocketServer}=require('ws');
const RK=['A','2','3','4','5','6','7','8','9','10','J','Q','K'],SU='♠♥♦♣';
const name=c=>c.j?'Coringa':RK[c.r]+SU[c.s];

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

function deal(R){
  const d=[];
  for(let k=0;k<2;k++)for(let s=0;s<4;s++)for(let r=0;r<13;r++)d.push({r,s,id:d.length});
  for(let i=0;i<4;i++)d.push({j:1,id:d.length});
  for(let i=d.length-1;i>0;i--){const j=Math.random()*(i+1)|0;[d[i],d[j]]=[d[j],d[i]]}
  R.players.forEach(p=>p.h=d.splice(0,9));
  R.stock=d;R.disc=[d.pop()];R.turn=Math.random()*R.players.length|0;
  R.phase='draw';R.win=-1;R.started=true;
  R.msg=`${R.players[R.turn].n} começa.`;
  loop(R);
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
  if(covered(p.h)==9){R.win=R.turn;R.msg=`🏆 ${p.n} bateu descartando ${name(c)}!`;return send(R)}
  R.msg=`${p.n} descartou ${name(c)}.`;
  R.turn=(R.turn+1)%R.players.length;R.phase='draw';loop(R);
}
function step(R){
  const p=R.players[R.turn];
  if(R.win>=0||!R.started||!auto(p))return;
  if(R.phase=='draw'){
    const bd=bestDiscard(p.h.concat([topCard(R)]));
    draw(R,bd.win||bd.sc>score(p.h)?'disc':'stock');
    send(R);setTimeout(()=>step(R),900);
  }else{const b=bestDiscard(p.h);discard(R,p.h[b.i].id)}
}
function loop(R){
  send(R);
  if(R.win>=0)return;
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
  return{t:'state',code:R.code,started:R.started,me:i,
    players:R.players.map(p=>({n:p.n,bot:!!p.bot,off:!p.bot&&!p.ws,c:p.h?p.h.length:0})),
    hand:R.players[i].h||[],top:R.disc&&topCard(R),stock:R.stock?R.stock.length:0,
    turn:R.turn,phase:R.phase,win:R.win,msg:R.msg,hint:hint(R,i),
    melds:R.win>=0?part(R.players[R.win].h):null};
}
function send(R){
  pushRooms();
  R.players.forEach((p,i)=>{if(p.ws&&p.ws.readyState==1)p.ws.send(JSON.stringify(view(R,i)))});
}

// ---------- servidor ----------
const html=fs.readFileSync(path.join(__dirname,'index.html'));
const server=http.createServer((q,r)=>{r.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});r.end(html)});
const wss=new WebSocketServer({server});
const clean=(s,n)=>String(s||'').replace(/[<>&"'`]/g,'').trim().slice(0,n);
const rawSend=(ws,o)=>{if(ws.readyState==1)ws.send(JSON.stringify(o))};
const err=(ws,m)=>rawSend(ws,{t:'err',m});
const listRooms=()=>Object.values(rooms).map(R=>({code:R.code,lock:!!R.pass,n:R.players.length,playing:R.started&&R.win<0}));
let lt=null;
function pushRooms(){clearTimeout(lt);lt=setTimeout(()=>{const l=listRooms();wss.clients.forEach(c=>{if(!c.inRoom)rawSend(c,{t:'rooms',list:l})})},150)}
const cast=(R,o)=>R.players.forEach(p=>p.ws&&rawSend(p.ws,o));

wss.on('connection',ws=>{
  let R=null,me=null;
  rawSend(ws,{t:'rooms',list:listRooms()});
  function leave(){
    if(!R)return;
    if(me.ws&&me.ws!==ws){R=null;me=null;return} // já reconectou em outra aba/conexão
    const r=R,p=me;R=null;me=null;ws.inRoom=false;
    if(!r.started||r.win>=0){
      r.players=r.players.filter(x=>x!==p);
      r.players.sort((a,b)=>!!a.bot-!!b.bot); // anfitrião sempre humano
      r.started=false;r.win=-1;r.msg='Aguardando jogadores.';
      if(!r.players.some(x=>!x.bot)){delete rooms[r.code];return pushRooms()}
      return send(r);
    }
    p.ws=null; // no meio da partida: vaga fica reservada e o bot joga até voltar
    if(r.players[r.turn]===p)loop(r);else send(r);
    setTimeout(()=>{if(rooms[r.code]===r&&r.players.every(x=>x.bot||!x.ws)){delete rooms[r.code];pushRooms()}},600000);
  }
  ws.on('message',raw=>{
    let m;try{m=JSON.parse(raw)}catch{return}
    if(m.t=='join'){
      if(R)return;
      const code=String(m.room||'').toUpperCase().replace(/[^A-Z0-9_-]/g,'').slice(0,14);
      if(!code)return err(ws,'Informe um nome para a sala.');
      let r=rooms[code];
      if(!r){
        if(!m.create)return err(ws,'Essa sala não existe mais.');
        r=rooms[code]={code,pass:clean(m.pass,20),players:[],started:false,win:-1,msg:'Aguardando jogadores.',chat:[]};
      }else if(m.create)return err(ws,'Já existe uma sala com esse nome.');
      let p=r.players.find(x=>!x.bot&&x.tok==m.tok);
      if(!p){
        if(r.pass&&clean(m.pass,20)!==r.pass)return err(ws,'Senha incorreta.');
        if(r.started&&r.win<0)return err(ws,'Partida em andamento nessa sala.');
        if(r.players.length>=10)return err(ws,'Mesa cheia (10 lugares).');
        p={n:clean(m.name,12)||'Jogador',tok:m.tok,ws};r.players.push(p);
      }else{if(p.ws&&p.ws!==ws)p.ws.close();p.ws=ws}
      R=r;me=p;ws.inRoom=true;
      rawSend(ws,{t:'chatlog',log:r.chat});
      if(r.started&&r.win<0&&r.players[r.turn]===p)return loop(r);
      return send(r);
    }
    if(!R||!me)return;
    if(m.t=='leave'){leave();rawSend(ws,{t:'left'});return rawSend(ws,{t:'rooms',list:listRooms()})}
    if(m.t=='chat'){
      const text=String(m.text||'').trim().slice(0,200);if(!text)return;
      const e={n:me.n,text};R.chat.push(e);if(R.chat.length>60)R.chat.shift();
      return cast(R,{t:'chat',m:e});
    }
    const i=R.players.indexOf(me),host=i==0,over=!R.started||R.win>=0;
    if(m.t=='bot'&&host&&over&&R.players.length<10){
      const k=R.players.filter(p=>p.bot).length+1;
      R.players.push({n:'Bot '+k,bot:1});R.started=false;R.win=-1;R.msg='Aguardando jogadores.';send(R);
    }else if(m.t=='start'&&host&&over&&R.players.length>=2)deal(R);
    else if(R.started&&R.win<0&&R.turn==i){
      if(m.t=='draw'&&R.phase=='draw'){draw(R,m.src=='disc'?'disc':'stock');send(R)}
      else if(m.t=='discard'&&R.phase=='discard')discard(R,m.id);
    }
  });
  ws.on('close',leave);
});
setInterval(()=>wss.clients.forEach(c=>c.ping()),25000);
const PORT=process.env.PORT||3000;
server.listen(PORT,()=>console.log('Pife online em http://localhost:'+PORT));
