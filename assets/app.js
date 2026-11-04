(function(){
"use strict";
const STUB={innerHTML:"",textContent:"",value:"",hidden:false,checked:false,dataset:{},style:{},addEventListener(){},setAttribute(){},removeAttribute(){},querySelectorAll(){return[]},closest(){return null}};
const $=id=>document.getElementById(id)||STUB;
const ROOT=document.body.dataset.root||"";
const PAGE=document.body.dataset.page||"inicio";
function boot(DATA){
const TEAMS=DATA.teams, PR=DATA.params, FX=DATA.fixtures, CUPS=DATA.cups, FOREIGN=DATA.foreign;
const N=TEAMS.length, MU=PR.mu, HOME=PR.home, RHO=PR.rho, SIGMA=PR.sigma, SIMS=20000;
const IX={};TEAMS.forEach((t,i)=>IX[t.name]=i);
const CUPORDER=["Libertadores","Sul-Americana","Copa do Brasil"];
const ABBR={"Estudiantes":"EST","Boca Juniors":"BOC","Montevideo City Torque":"MCT"};
const code=n=>n in IX?TEAMS[IX[n]].code:(ABBR[n]||n.slice(0,3).toUpperCase());
const WATCH="a confirmar";

// ---------- utilidades ----------
function rng(seed){return function(){seed|=0;seed=seed+0x6D2B79F5|0;let t=Math.imul(seed^seed>>>15,1|seed);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
function poisson(l,u){const L=Math.exp(-l);let k=0,p=1;do{k++;p*=u()}while(p>L);return k-1}
function gauss(u){return Math.sqrt(-2*Math.log(u()||1e-12))*Math.cos(2*Math.PI*u())}
const FACT=[1];for(let k=1;k<11;k++)FACT[k]=FACT[k-1]*k;
function dist(l,m,rho){let W=0,D=0,L=0,bp=-1,best=[0,0];
 for(let x=0;x<11;x++)for(let y=0;y<11;y++){let t=1;if(x===0&&y===0)t=1-l*m*rho;else if(x===0&&y===1)t=1+l*rho;else if(x===1&&y===0)t=1+m*rho;else if(x===1&&y===1)t=1-rho;
  const p=Math.max(0,t)*Math.pow(l,x)*Math.exp(-l)/FACT[x]*Math.pow(m,y)*Math.exp(-m)/FACT[y];if(x>y)W+=p;else if(x===y)D+=p;else L+=p;if(p>bp){bp=p;best=[x,y];}}
 const s=W+D+L;return{W:W/s,D:D/s,L:L/s,best,bestP:bp/s,l,m};}
const lamAB=(h,a)=>[Math.exp(MU+HOME+TEAMS[h].att-TEAMS[a].dfn),Math.exp(MU+TEAMS[a].att-TEAMS[h].dfn)];
const dA=(h,a)=>{const [l,m]=lamAB(h,a);return dist(l,m,RHO);};
const nf1=new Intl.NumberFormat("pt-BR",{maximumFractionDigits:1,minimumFractionDigits:1}),nf0=new Intl.NumberFormat("pt-BR",{maximumFractionDigits:0}),nf2=new Intl.NumberFormat("pt-BR",{minimumFractionDigits:2,maximumFractionDigits:2}),nf3=new Intl.NumberFormat("pt-BR",{minimumFractionDigits:3,maximumFractionDigits:3});
function pct(x){if(x===0)return"—";if(x<.001)return"<0,1%";if(x>.999&&x<1)return">99,9%";if(x===1)return"100%";const v=x*100;return(v<10?nf1.format(v):nf0.format(v))+"%";}
const pct1=x=>nf1.format(x*100)+"%";
const nf4=new Intl.NumberFormat("pt-BR",{minimumFractionDigits:4,maximumFractionDigits:4});
const brl=v=>"R$ "+nf2.format(v);
const oneIn=p=>p>0?"1 em "+nf0.format(Math.round(1/p)):"—";
const esc=s=>String(s).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));
const T=i=>TEAMS[i];
function wdlBar(hn,an,hc,ac,d){return`<div class="wdl"><div class="bar" role="img" aria-label="${esc(hn)} ${pct(d.W)}, empate ${pct(d.D)}, ${esc(an)} ${pct(d.L)}"><i class="w" style="width:${d.W*100}%"></i><i class="d" style="width:${d.D*100}%"></i><i class="l" style="width:${d.L*100}%"></i></div><div class="lbl num"><span><b>${pct(d.W)}</b> ${hc}</span><span>Empate <b>${pct(d.D)}</b></span><span>${ac} <b>${pct(d.L)}</b></span></div></div>`;}

// ---------- motor de simulação ----------
const rcount={};FX.forEach(f=>rcount[f.r]=(rcount[f.r]||0)+1);const NEXTA=Math.min(...Object.keys(rcount).map(Number).filter(r=>rcount[r]>=3));
const R32=FX.map((f,i)=>i).filter(i=>FX[i].r===NEXTA), TRACK=FX.map((f,i)=>i).filter(i=>FX[i].r===NEXTA||FX[i].r===NEXTA+1);
const fixed={}; // índice do jogo -> 0 casa, 1 empate, 2 fora
const cupFixed={"Libertadores":null,"Sul-Americana":null,"Copa do Brasil":null};
let result=null, prevSig=null;

function simulate(){
 const u=rng(31337), title=new Float64Array(N), lib=new Float64Array(N), sula=new Float64Array(N), z4=new Float64Array(N), cut=new Float64Array(N+1);
 const cupCnt={},cupFin={},rep={};CUPORDER.forEach(c=>{cupCnt[c]={};cupFin[c]={};rep[c]=0;});
 const oc=TRACK.map(()=>[0,0,0]), lv=TRACK.map(()=>[0,1,2].map(()=>[[0,0,0],[0,0,0]]));
 const A=new Float64Array(N),Dm=new Float64Array(N),P=new Float64Array(N),V=new Float64Array(N),SG=new Float64Array(N),GP=new Float64Array(N),tb=new Float64Array(N);
 const idx=TEAMS.map((t,i)=>i), outc=new Int8Array(FX.length), Q=new Uint8Array(N);
 const str=(n)=>n in IX?[A[IX[n]],Dm[IX[n]]]:[FOREIGN[n],FOREIGN[n]];
 const play=(a,b,home)=>{const [aa,ad]=str(a),[ba,bd]=str(b);return[poisson(Math.exp(MU+aa-bd+(home==="a"?HOME:0)),u),poisson(Math.exp(MU+ba-ad+(home==="b"?HOME:0)),u)];};
 const tie=(t)=>{if(t.vencedor)return t.vencedor;let x1,y1,x2,y2;
  if(!t.ida){[x1,y1]=play(t.a,t.b,"a");[y2,x2]=play(t.b,t.a,"a");}else{[x1,y1]=t.ida;[x2,y2]=play(t.a,t.b,t.volta_casa===t.a?"a":"b");}
  const sa=x1+x2,sb=y1+y2;if(sa!==sb)return sa>sb?t.a:t.b;return u()<.5?t.a:t.b;};
 const fin=(a,b)=>{const [x,y]=play(a,b,null);if(x!==y)return x>y?[a,b]:[b,a];return u()<.5?[a,b]:[b,a];};
 for(let s=0;s<SIMS;s++){
  for(let i=0;i<N;i++){const t=TEAMS[i];A[i]=t.att+SIGMA*gauss(u);Dm[i]=t.dfn+SIGMA*gauss(u);P[i]=t.pts;V[i]=t.v;SG[i]=t.gp-t.gc;GP[i]=t.gp;tb[i]=u();}
  for(let k=0;k<FX.length;k++){const f=FX[k],h=f.h,a=f.a;let gh,ga;
   if(fixed[k]!==undefined){gh=fixed[k]===2?0:1;ga=fixed[k]===0?0:1;}
   else{gh=poisson(Math.exp(MU+HOME+A[h]-Dm[a]),u);ga=poisson(Math.exp(MU+A[a]-Dm[h]),u);}
   if(gh>ga){P[h]+=3;V[h]++;}else if(gh<ga){P[a]+=3;V[a]++;}else{P[h]++;P[a]++;}
   SG[h]+=gh-ga;SG[a]+=ga-gh;GP[h]+=gh;GP[a]+=ga;outc[k]=gh>ga?0:gh===ga?1:2;}
  idx.sort((x,y)=>P[y]-P[x]||V[y]-V[x]||SG[y]-SG[x]||GP[y]-GP[x]||tb[y]-tb[x]);
  const pos=new Int32Array(N);for(let p=0;p<N;p++)pos[idx[p]]=p;
  title[idx[0]]++;for(let p=16;p<N;p++)z4[idx[p]]++;
  const ch={};
  for(const c of CUPORDER){const S=CUPS[c].semis;const w1=tie(S[0]),w2=tie(S[1]);let champ,vice;
   if(cupFixed[c]!==null){champ=cupFixed[c];vice=(champ===S[0].a||champ===S[0].b)?w2:w1;}else{[champ,vice]=fin(w1,w2);}
   ch[c]=[champ,vice];cupCnt[c][champ]=(cupCnt[c][champ]||0)+1;for(const f of [w1,w2])cupFin[c][f]=(cupFin[c][f]||0)+1;
   if(champ in IX&&pos[IX[champ]]<5)rep[c]++;}
  // Libertadores 2027 (regra CBF 2026): 5 vagas pela tabela + campeão e vice da Copa do Brasil; campeões brasileiros da Libertadores e da Sul-Americana somam vaga; quem já tem vaga repassa ao próximo.
  Q.fill(0);let slots=7,count=0;const special=[ch["Copa do Brasil"][0],ch["Copa do Brasil"][1]];
  for(const c of ["Libertadores","Sul-Americana"])if(ch[c][0] in IX){special.push(ch[c][0]);slots++;}
  for(const n of special){const i=IX[n];if(i!==undefined&&!Q[i]){Q[i]=1;count++;}}
  let c_=0;for(let p=0;p<N&&count<slots;p++){const t=idx[p];if(!Q[t]){Q[t]=1;count++;c_=p+1;}}
  cut[c_]++;
  let ns=0;for(let p=0;p<16&&ns<6;p++){const t=idx[p];if(!Q[t]){sula[t]++;ns++;}}
  for(let i=0;i<N;i++)lib[i]+=Q[i];
  for(let m=0;m<TRACK.length;m++){const k=TRACK[m],o=outc[k];oc[m][o]++;for(let sd=0;sd<2;sd++){const t=sd===0?FX[k].h:FX[k].a,p=pos[t],L=lv[m][o][sd];if(p===0)L[0]++;if(Q[t])L[1]++;if(p>=16)L[2]++;}}}
 const prob=TEAMS.map((t,i)=>({title:title[i]/SIMS,lib:lib[i]/SIMS,sula:sula[i]/SIMS,z4:z4[i]/SIMS}));
 const OBJ=["título","Libertadores","rebaixamento"];
 const levs=TRACK.map((k,m)=>{if(fixed[k]!==undefined)return null;let best=null;
  for(let sd=0;sd<2;sd++){const wi=sd===0?0:2,lo=sd===0?2:0;if(oc[m][wi]<300||oc[m][lo]<300)continue;
   for(let j=0;j<3;j++){const pw=lv[m][wi][sd][j]/oc[m][wi],pl=lv[m][lo][sd][j]/oc[m][lo],d=Math.abs(pw-pl);if(!best||d>best.d)best={d,team:sd===0?FX[k].h:FX[k].a,obj:OBJ[j],pw,pl};}}
  return best&&{k,...best};}).filter(Boolean).sort((a,b)=>b.d-a.d);
 const cups={},finals={},repasse={};CUPORDER.forEach(c=>{cups[c]={};finals[c]={};for(const n in cupCnt[c])cups[c][n]=cupCnt[c][n]/SIMS;for(const n in cupFin[c])finals[c][n]=cupFin[c][n]/SIMS;repasse[c]=rep[c]/SIMS;});
 return{prob,levs,cut:Array.from(cut,x=>x/SIMS),cups,finals,repasse};
}

// ---------- Brasileirão ----------
const curOrder=TEAMS.map((t,i)=>i);
function renderTitle(prob){const top=TEAMS.map((t,i)=>({t,p:prob[i].title})).sort((a,b)=>b.p-a.p).slice(0,5);const max=Math.max(top[0].p,.01);
 $("titlebars").innerHTML=top.map(o=>`<div class="tbar"><span>${esc(o.t.name)}</span><span class="track" role="img" aria-label="${esc(o.t.name)}: ${pct(o.p)}"><span class="fill" style="width:${(o.p/max*100).toFixed(1)}%"></span></span><span class="v num">${pct(o.p)}</span></div>`).join("");}
function renderTable(prob){const prev=prevSig;
 $("tbody").innerHTML=curOrder.map((ti,p)=>{const t=T(ti),pr=prob[ti],gd=t.gp-t.gc;
  const zc=p>=16?"var(--z4)":pr.lib>.5?"var(--g6)":pr.sula>.5?"var(--sula)":"transparent";
  const cell=(x,c)=>`<td class="p c-${c}${x===0?" zero":""}"><i class="pb" style="--w:${(x*100).toFixed(1)}%"></i><span class="num">${pct(x)}</span></td>`;
  const ch=prev&&Math.abs(prev[ti]-(pr.title+pr.z4+pr.lib))>.02?' class="changed"':"";
  return`<tr${ch}><td class="pos num"><span class="z" style="background:${zc}"></span>${p+1}</td><td class="team">${esc(t.name)}</td><td class="pts num">${t.pts}</td><td class="num">${t.j}</td><td class="num">${gd>0?"+":""}${gd}</td>${cell(pr.title,"title")}${cell(pr.lib,"g6")}${cell(pr.sula,"sula")}${cell(pr.z4,"z4")}</tr>`;}).join("");
 prevSig=prob.map(p=>p.title+p.z4+p.lib);}
function renderCut(cut){let best=0;for(let g=1;g<cut.length;g++)if(cut[g]>cut[best])best=g;const it=[];
 for(let g=1;g<cut.length;g++)if(cut[g]>=.005)it.push(`<div class="g${g===best?" top":""}"><b class="num">G${g}</b><span class="num">${pct(cut[g])}</span></div>`);
 $("cut").innerHTML=`<span class="lab">Até onde a tabela leva à Libertadores 2027:</span>${it.join("")}`;}
function renderFixtures(){$("fixtures").innerHTML=R32.map(k=>{const f=FX[k],h=f.h,a=f.a,v=fixed[k];
 const b=(val,txt)=>`<button type="button" data-m="${k}" data-v="${val}" aria-pressed="${String(val==="auto"?v===undefined:v===val)}">${txt}</button>`;
 return`<div class="fxrow"><div class="fxhead"><span>${esc(T(h).name)} x ${esc(T(a).name)}</span><span class="muted">${esc(f.data)}</span></div>${wdlBar(T(h).name,T(a).name,T(h).code,T(a).code,dA(h,a))}<div class="seg" role="group" aria-label="Resultado de ${esc(T(h).name)} x ${esc(T(a).name)}">${b("auto","Modelo")}${b(0,T(h).code)}${b(1,"Empate")}${b(2,T(a).code)}</div></div>`;}).join("");}
function renderCups(cp){$("cups").innerHTML=CUPORDER.map(c=>{const S=CUPS[c].semis,v=cupFixed[c],names=S.flatMap(t=>t.vencedor?[t.vencedor]:[t.a,t.b]);
 const desc=S.map(t=>t.vencedor?`${code(t.vencedor)} na final`:`${code(t.a)} x ${code(t.b)}${t.ida?` (ida ${t.ida[0]}–${t.ida[1]})`:""}`).join(" · ");
 const b=(val,txt,title)=>`<button type="button" data-c="${c}" data-v="${esc(val)}" title="${esc(title)}" aria-pressed="${String(val==="auto"?v===null:v===val)}">${txt}</button>`;
 const lead=cp?Object.entries(cp[c]).sort((x,y)=>y[1]-x[1])[0]:null;
 return`<div class="fxrow"><div class="fxhead"><span>${c} · campeão</span><span class="muted">${lead&&v===null?`${code(lead[0])} ${pct(lead[1])}`:""}</span></div><div class="note">Semifinais: ${desc}</div><div class="seg" style="grid-template-columns:repeat(${names.length+1},1fr)" role="group" aria-label="Campeão da ${c}">${b("auto","Modelo","Deixar o modelo decidir")}${names.map(n=>b(n,code(n),n)).join("")}</div></div>`;}).join("");}

function run(){$("status").textContent="Simulando…";
 setTimeout(()=>{const t0=performance.now();result=simulate();const ms=Math.round(performance.now()-t0);
  renderTitle(result.prob);renderTable(result.prob);renderCut(result.cut);renderCups(result.cups);renderGames();renderTiles();renderCupViews();
  const nf=Object.keys(fixed).length+CUPORDER.filter(c=>cupFixed[c]!==null).length;
  $("status").textContent=`${nf0.format(SIMS)} temporadas simuladas em ${ms} ms${nf?` · ${nf} escolha${nf>1?"s":""} sua${nf>1?"s":""}`:""}`;
  $("tc-sub").textContent=nf?`Seu cenário: ${nf} resultado${nf>1?"s":""} fixado${nf>1?"s":""}`:`${nf0.format(SIMS)} temporadas simuladas no seu navegador`;},20);}
$("fixtures").addEventListener("click",e=>{const b=e.target.closest("button[data-m]");if(!b)return;const k=+b.dataset.m,v=b.dataset.v;if(v==="auto")delete fixed[k];else fixed[k]=+v;
 b.parentElement.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",String(x===b)));run();});
$("cups").addEventListener("click",e=>{const b=e.target.closest("button[data-c]");if(!b)return;const c=b.dataset.c,v=b.dataset.v;cupFixed[c]=v==="auto"?null:v;
 b.parentElement.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",String(x===b)));run();});
$("run").addEventListener("click",run);
$("reset").addEventListener("click",()=>{for(const k in fixed)delete fixed[k];CUPORDER.forEach(c=>cupFixed[c]=null);renderFixtures();run();});

// ---------- Jogos da semana ----------
let gFilter="todos";
function allLevs(){if(!result||!resB)return[];return[...result.levs.map(L=>({...L,lg:"A"})),...resB.levs.map(L=>({...L,lg:"B"}))].sort((a,b)=>b.d-a.d);}
function renderGames(){if(!result||!resB)return;const lev=new Map(allLevs().map((L,i)=>[L.lg+L.k,{...L,rank:i}]));
 let list=[...TRACK.map(k=>({lg:"A",k})),...BTRACK.map(k=>({lg:"B",k}))];
 if(gFilter==="decisivos")list=list.filter(g=>lev.has(g.lg+g.k)).sort((a,b)=>lev.get(a.lg+a.k).rank-lev.get(b.lg+b.k).rank).slice(0,6);
 else if(gFilter!=="todos")list=list.filter(g=>g.lg===gFilter);
 $("games").innerHTML=list.map(({lg,k})=>{const isA=lg==="A",f=isA?FX[k]:BFX[k],TT=isA?T:TB,h=f.h,a=f.a,d=isA?dA(h,a):dB(h,a),L=lev.get(lg+k);
  return`<article class="game"><div class="meta"><span>Série ${lg} · ${f.r}ª rodada · ${esc(f.data)}</span>${L&&L.rank<3?`<span class="tag">Decisivo nº ${L.rank+1}</span>`:""}</div>
  <div class="teams"><span>${esc(TT(h).name)}</span><span class="x">x</span><span>${esc(TT(a).name)}</span></div>${wdlBar(TT(h).name,TT(a).name,TT(h).code,TT(a).code,d)}
  <div class="facts"><div class="fact">Placar mais provável<b class="num">${d.best[0]} x ${d.best[1]}</b>${pct(d.bestP)}</div><div class="fact">Gols esperados<b class="num">${nf1.format(d.l)} x ${nf1.format(d.m)}</b>média do modelo</div></div>
  ${L?`<div class="lev"><strong class="num">${nf0.format(L.d*100)} p.p.</strong>${esc(TT(L.team).name)}: chance de ${L.obj} vai de <b class="num">${pct(L.pl)}</b> com derrota a <b class="num">${pct(L.pw)}</b> com vitória</div>`:""}
  <div class="watch">Onde assistir: <b>${WATCH}</b></div></article>`;}).join("")||`<p class="status">Nenhum jogo neste filtro.</p>`;}
document.querySelector('[data-view="jogos"] .filters')?.addEventListener("click",e=>{const b=e.target.closest("button[data-f]");if(!b)return;gFilter=b.dataset.f;
 b.parentElement.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",String(x===b)));renderGames();});

// ---------- Rankings ----------
let rk="cbf";
const TBL=(head,rows)=>`<table><thead><tr>${head.map(h=>`<th${h.l?' class="l"':""}>${h.t}</th>`).join("")}</tr></thead><tbody>${rows.join("")}</tbody></table>`;
const bar=(x,mx,col)=>`<span class="rankbar" style="width:${(4+Math.max(0,x)/mx*80).toFixed(0)}px${col?`;background:${col}`:""}"></span>`;
function renderRank(){const R=DATA.rankings||{};let h="",note="";
 if(rk==="A"||rk==="B"){const isA=rk==="A",L=isA?TEAMS:BT,mu=isA?MU:BP.mu;
  const rows=L.map(t=>{const gf=Math.exp(mu+t.att),ga=Math.exp(mu-t.dfn);return{t,gf,ga,s:gf-ga};}).sort((a,b)=>b.s-a.s);const mx=Math.max(...rows.map(r=>Math.abs(r.s)),.01);
  h=TBL([{t:"#"},{t:"Clube",l:1},{t:"Gols feitos"},{t:"Gols sofridos"},{t:"Saldo esperado"}],rows.map((r,i)=>`<tr><td class="num">${i+1}</td><td class="team">${esc(r.t.name)}</td><td class="num">${nf2.format(r.gf)}</td><td class="num">${nf2.format(r.ga)}</td><td class="num">${bar(Math.abs(r.s),mx,r.s>=0?"var(--g6)":"var(--z4)")}<b>${r.s>0?"+":""}${nf2.format(r.s)}</b></td></tr>`));
  note=isA?"Força do modelo: gols por jogo contra um adversário médio da Série A, em campo neutro.":"Força do modelo: gols por jogo contra um adversário médio da Série B, em campo neutro. A escala não é comparável com a da Série A.";}
 else if(rk==="cbf"){const C=R.cbf,mx=C.clubes[0].oficial;
  h=TBL([{t:"#"},{t:"Clube",l:1},{t:"Pontos oficiais"},{t:"Série A recalculada"},{t:"Demais competições"}],C.clubes.map(r=>`<tr><td class="num">${r.pos}</td><td class="team">${esc(r.clube)}</td><td class="num">${bar(r.oficial,mx)}<b>${nf0.format(r.oficial)}</b></td><td class="num">${r.serieA?nf0.format(r.serieA):"—"}</td><td class="num muted">${nf0.format(r.resto)}</td></tr>`));
  const hz=C.hipoteses[C.escolhida];
  note=`Ranking Nacional de Clubes 2026, publicado pela CBF em dezembro de 2025 (60 primeiros de 235). Soma os pontos de 2021 a 2025 com peso 1 a 5, do ano mais antigo ao mais recente. Recalculamos a parte da Série A com a nossa base, com 800, 640, 600 e 560 pontos do 1º ao 4º e 8 a menos por posição a partir do 5º (552): ela explica ${pct(hz.parcela)} dos pontos dos clubes que jogaram a Série A no período, com correlação de postos de ${nf2.format(hz.spearman)} com o total oficial. O resto vem da Copa do Brasil e das Séries B, C e D, que a base não cobre jogo a jogo.`;}
 else if(rk==="conmebol"){const C=R.conmebol,mx=C[0].total;
  h=TBL([{t:"#"},{t:"Clube",l:1},{t:"País",l:1},{t:"Histórico"},{t:"Desempenho"},{t:"Total"}],C.map(r=>`<tr${r.pais==="Brasil"?' style="background:color-mix(in srgb,var(--canarinho) 12%,transparent)"':""}><td class="num">${r.pos}</td><td class="team">${esc(r.clube)}</td><td class="l">${esc(r.pais)}</td><td class="num">${nf1.format(r.hist)}</td><td class="num">${nf1.format(r.perf)}</td><td class="num">${bar(r.total,mx)}<b>${nf1.format(r.total)}</b></td></tr>`));
  note="Ranking de Clubes Conmebol 2026, publicado em 15/12/2025 (50 primeiros). Soma pontos históricos de Libertadores e Sul-Americana e pontos de desempenho recente. A nossa base não tem os jogos das copas sul-americanas, por isso este ranking é mostrado como publicado, sem recálculo. Brasileiros destacados.";}
 else if(rk==="fifa"){const F=R.fifa,mx=F.recalculo[0].pontos;const off=new Map(F.oficial_out.map(r=>[r.selecao,r]));
  h=`<div class="two" style="gap:16px">${TBL([{t:"#"},{t:"Seleção",l:1},{t:"Oficial 07/10/2026"},{t:"Nosso recálculo"},{t:"Nossa posição"}],F.comparacao.filter(r=>r.oficial).map(r=>`<tr><td class="num">${r.oficial_pos}</td><td class="team">${esc(r.selecao)}</td><td class="num"><b>${nf2.format(r.oficial)}</b></td><td class="num">${nf2.format(r.nosso)}</td><td class="num ${r.nosso_pos===r.oficial_pos?"ok":""}">${r.nosso_pos}º</td></tr>`))}
   ${TBL([{t:"#"},{t:"Seleção (recálculo)",l:1},{t:"Pontos"}],F.recalculo.slice(0,30).map(r=>`<tr><td class="num">${r.pos}</td><td class="team">${esc(r.selecao)}</td><td class="num">${bar(r.pontos-1400,mx-1400)}${nf2.format(r.pontos)}</td></tr>`))}</div>`;
  note=`Ranking FIFA masculino oficial de 07/10/2026 (próximo: 18/11/2026) e o nosso recálculo pela fórmula SUM: P = P anterior + I × (W − We), com We = 1/(10^(−dr/600)+1). Partimos do ranking oficial de 11/06/2026, aplicamos os ${nf0.format(F.jogos)} jogos da base até 06/10 (Copa do Mundo, Liga das Nações, eliminatórias e amistosos) e acertamos a ordem exata dos 9 primeiros. Erro médio de ${nf1.format(F.mae_top10)} pontos no top 10; correlação de postos de ${nf3.format(F.spearman)} nas ${F.comparacao.length} posições publicadas. Diferenças: a base não registra disputas de pênaltis, e seleções fora do top 20 de junho partiram de pontos estimados pelo nosso Elo.`;}
 else if(rk==="hist"){const H=R.historico.brasileirao,mx=H[0].pts;
  h=TBL([{t:"#"},{t:"Clube",l:1},{t:"Temporadas"},{t:"Pts"},{t:"J"},{t:"V"},{t:"E"},{t:"D"},{t:"SG"},{t:"Aprov."},{t:"Títulos"}],H.slice(0,50).map((r,i)=>`<tr><td class="num">${i+1}</td><td class="team">${esc(r.clube)}</td><td class="num">${r.temporadas}</td><td class="num">${bar(r.pts,mx)}<b>${nf0.format(r.pts)}</b></td><td class="num">${r.j}</td><td class="num">${r.v}</td><td class="num">${r.e}</td><td class="num">${r.d}</td><td class="num">${r.gp-r.gc>0?"+":""}${r.gp-r.gc}</td><td class="num">${pct(r.aprov)}</td><td class="num">${r.titulos||"—"}</td></tr>`));
  note=`Classificação de todos os jogos da Série A por pontos corridos, de 2003 a 2026 (2026 até 04/11): ${nf0.format(R.historico.jogos_br)} jogos da nossa base, vitória valendo 3 pontos em todas as temporadas. Títulos contam só a era dos pontos corridos.`;}
 else if(rk==="sel"){const H=R.historico.selecoes,mx=H[0].pts;
  h=TBL([{t:"#"},{t:"Seleção",l:1},{t:"Pts"},{t:"J"},{t:"V"},{t:"E"},{t:"D"},{t:"Gols"},{t:"Aprov."}],H.slice(0,50).map((r,i)=>`<tr><td class="num">${i+1}</td><td class="team">${esc(r.selecao)}</td><td class="num">${bar(r.pts,mx)}<b>${nf0.format(r.pts)}</b></td><td class="num">${nf0.format(r.j)}</td><td class="num">${r.v}</td><td class="num">${r.e}</td><td class="num">${r.d}</td><td class="num">${r.gp}:${r.gc}</td><td class="num">${pct(r.aprov)}</td></tr>`));
  note=`Todos os ${nf0.format(R.historico.jogos_sel)} jogos oficiais e amistosos de seleções da base (${R.historico.periodo_sel[0].slice(0,4)} a ${R.historico.periodo_sel[1].slice(0,4)}), com vitória valendo 3 pontos. Só seleções com 100 jogos ou mais.`;}
 $("rankbox").innerHTML=h;$("ranknote").textContent=note;}
document.querySelector('[data-view="rankings"] .tabs')?.addEventListener("click",e=>{const b=e.target.closest("button[data-rk]");if(!b)return;rk=b.dataset.rk;
 b.parentElement.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",String(x===b)));renderRank();});

// ---------- Copa do Brasil, Libertadores, Sul-Americana ----------
const CUPINFO=DATA.cupinfo||{};
const CUPVIEW={"copa-do-brasil":"Copa do Brasil","libertadores":"Libertadores","sul-americana":"Sul-Americana"};
function renderCupViews(){if(!result)return;for(const v in CUPVIEW){const c=CUPVIEW[v],el=$("cv-"+v);if(!el)continue;const I=CUPINFO[c]||{};
 const ch=Object.entries(result.cups[c]).sort((a,b)=>b[1]-a[1]),fi=result.finals[c],mx=Math.max(ch[0][1],.01);
 const teams=[...new Set(CUPS[c].semis.flatMap(t=>[t.a,t.b]))];
 const rows=teams.map(n=>({n,c:result.cups[c][n]||0,f:fi[n]||0})).sort((a,b)=>b.c-a.c||b.f-a.f);
 el.innerHTML=`<div class="board"><div class="card tablebox"><div class="scroll">${TBL([{t:"Clube",l:1},{t:"Final"},{t:"Título"}],rows.map(r=>`<tr><td class="team">${esc(r.n)}${r.n in IX?"":' <span class="muted">(estrangeiro)</span>'}</td><td class="p c-sula"><i class="pb" style="--w:${(r.f*100).toFixed(1)}%"></i><span class="num">${r.f>=.9995?"Na final":r.f===0?"Eliminado":pct(r.f)}</span></td><td class="p c-title"><i class="pb" style="--w:${(r.c*100).toFixed(1)}%"></i><span class="num">${pct(r.c)}</span></td></tr>`))}</div>
  <div class="legend"><span>${nf0.format(SIMS)} simulações no seu navegador, as mesmas da Série A</span></div></div>
  <div class="card sim"><div><div class="eyebrow">Chance de título</div><h3>Favoritos</h3></div><div class="tbars">${ch.slice(0,4).map(([n,p])=>`<div class="tbar"><span>${esc(n)}</span><span class="track"><span class="fill" style="width:${(p/mx*100).toFixed(1)}%"></span></span><span class="v num">${pct(p)}</span></div>`).join("")}</div>
  <div class="eyebrow">Semifinais</div>${(I.semis||[]).map(s=>`<div class="fxrow"><div class="fxhead"><span>${esc(s.a)} x ${esc(s.b)}</span><span class="muted">${s.done?"Decidida":"Em disputa"}</span></div><div class="note">${esc(s.txt)}</div></div>`).join("")}
  <div class="fxrow"><div class="fxhead"><span>Final</span></div><div class="note">${esc(I.final||"")}</div></div>
  <div class="fxrow"><div class="fxhead"><span>Efeito na Série A</span></div><div class="note">${esc(I.vagas||"")} ${c==="Copa do Brasil"?`Em ${pct(result.repasse[c])} das simulações o campeão já estaria entre os 5 primeiros da Série A, e a vaga desce para o próximo colocado.`:""}</div></div>
  <a class="btn ghost" href="${ROOT}serie-a/">Mudar resultados no simulador da Série A</a></div></div>`;}}

// ---------- Acerto 2026 (backtest rodada a rodada) ----------
let acS="A",acR=null;
function renderAcerto(){const BT=DATA.bt2026;if(!BT||!$("ac-kpis"))return;const S=BT[acS],css=getComputedStyle(document.documentElement),col=v=>css.getPropertyValue(v).trim()||"#888";
 $("ac-kpis").innerHTML=[["Acerto do palpite",pct1(S.acerto),`${nf0.format(Math.round(S.acerto*S.n))} de ${nf0.format(S.n)} jogos (IC 95%: ${pct(S.ic[0])}–${pct(S.ic[1])})`],["Dupla chance",pct1(S.dupla),"acerto com os 2 resultados mais prováveis"],["Sempre o mandante",pct1(S.ref_mandante),"referência: apostar sempre na vitória de quem joga em casa"],["Turno × returno",`${pct(S.turno)} · ${S.returno==null?"—":pct(S.returno)}`,"o modelo aprende com a temporada"],["Melhor rodada",`${S.melhor_rodada.acertos} de 10`,`${S.melhor_rodada.rodada}ª rodada; pior: ${S.pior_rodada.acertos} na ${S.pior_rodada.rodada}ª`]]
  .map(([k,v,x])=>`<div class="stat"><span class="k">${k}</span><span class="v num">${v}</span><span class="s">${x}</span></div>`).join("");
 // gráfico por rodada
 const R=S.por_rodada,W=900,H=260,L=40,Rr=40,Tp=16,Bt=34,bw=(W-L-Rr)/R.length,y=v=>Tp+(1-v/10)*(H-Tp-Bt),ya=v=>Tp+(1-v)*(H-Tp-Bt);
 $("ac-h").textContent=`Acertos em cada rodada (barras) e acerto acumulado (linha) · Série ${acS}`;
 $("ac-chart").innerHTML=`<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Acertos por rodada da Série ${acS} em 2026">
  ${[0,2,4,6,8,10].map(v=>`<line x1="${L}" x2="${W-Rr}" y1="${y(v)}" y2="${y(v)}" stroke="${col("--line")}"/><text x="${L-6}" y="${y(v)+4}" text-anchor="end" font-size="11" fill="${col("--muted")}" font-family="IBM Plex Mono, monospace">${v}</text>`).join("")}
  ${[.3,.4,.5,.6].map(v=>`<text x="${W-Rr+6}" y="${ya(v)+4}" font-size="11" fill="${col("--pitch")}" font-family="IBM Plex Mono, monospace">${v*100}%</text>`).join("")}
  <line x1="${L}" x2="${W-Rr}" y1="${ya(S.ref_mandante)}" y2="${ya(S.ref_mandante)}" stroke="${col("--loss")}" stroke-dasharray="4 4"/><text x="${W-Rr-4}" y="${Tp+10}" text-anchor="end" font-size="11" fill="${col("--loss")}">tracejado: sempre o mandante (${pct(S.ref_mandante)})</text>
  ${R.map((r,i)=>`<rect x="${(L+i*bw+bw*.15).toFixed(1)}" y="${y(r.acertos)}" width="${(bw*.7).toFixed(1)}" height="${(y(0)-y(r.acertos)).toFixed(1)}" fill="${col("--canarinho")}" opacity="${r.jogos<10?.45:.85}"><title>${r.rodada}ª rodada: ${r.acertos} de ${r.jogos}</title></rect>${i%3===0||i===R.length-1?`<text x="${(L+i*bw+bw/2).toFixed(1)}" y="${H-16}" text-anchor="middle" font-size="10" fill="${col("--muted")}" font-family="IBM Plex Mono, monospace">${r.rodada}</text>`:""}`).join("")}
  <path d="${R.map((r,i)=>`${i?"L":"M"}${(L+i*bw+bw/2).toFixed(1)} ${ya(r.acum_acerto).toFixed(1)}`).join("")}" fill="none" stroke="${col("--pitch")}" stroke-width="2.5"/>
  <text x="${(L+W-Rr)/2}" y="${H-2}" text-anchor="middle" font-size="11" fill="${col("--muted")}">rodada · barras: acertos (eixo à esquerda) · linha: acerto acumulado (eixo à direita)</text></svg>${R.some(r=>r.jogos<10)?`<p class="note">Barras claras: rodadas incompletas (${R.filter(r=>r.jogos<10).map(r=>`${r.rodada}ª com ${r.jogos} jogos`).join(", ")}).</p>`:""}`;
 $("ac-faixas").innerHTML=`<thead><tr><th class="l">Chance do palpite</th><th>Jogos</th><th>Confiança média</th><th>Acerto real</th></tr></thead><tbody>${S.faixas.map(f=>`<tr><td class="l">${f.faixa}</td><td class="num">${f.jogos}</td><td class="num">${pct(f.confianca)}</td><td class="num"><b>${pct(f.acerto)}</b></td></tr>`).join("")}</tbody>`;
 $("ac-fnote").textContent=`Resultados reais de 2026: ${pct(S.resultados.casa)} vitórias do mandante, ${pct(S.resultados.empate)} empates e ${pct(S.resultados.fora)} do visitante. O palpite único quase nunca é o empate (${pct1(S.palpites.empate)} dos jogos), porque o empate raramente é o resultado mais provável — é o principal motivo de nenhum modelo passar muito de 50%.`;
 // evolução
 const E=DATA.evol2026&&DATA.evol2026[acS];if(E){const key=acS==="A"?"titulo":"acesso",cl=Object.entries(E).sort((a,b)=>b[1][key][b[1][key].length-1]-a[1][key][a[1][key].length-1]).slice(0,acS==="A"?3:5);
  const rs=cl[0][1].rodada,EW=440,EH=240,el=36,er=110,et=10,eb=30,ex=r=>el+(r-rs[0])/(rs[rs.length-1]-rs[0])*(EW-el-er),ey=v=>et+(1-v)*(EH-et-eb);
  const pal=[col("--pitch"),col("--canarinho"),col("--sula"),col("--z4"),col("--muted")];
  $("ac-eh").textContent=acS==="A"?"Chance de título antes de cada rodada":"Chance de acesso antes de cada rodada";
  $("ac-evol").innerHTML=`<svg viewBox="0 0 ${EW} ${EH}" role="img" aria-label="Evolução das chances">${[0,.25,.5,.75,1].map(v=>`<line x1="${el}" x2="${EW-er}" y1="${ey(v)}" y2="${ey(v)}" stroke="${col("--line")}"/><text x="${el-6}" y="${ey(v)+4}" text-anchor="end" font-size="10" fill="${col("--muted")}" font-family="IBM Plex Mono, monospace">${v*100}%</text>`).join("")}
   ${cl.map(([n,v],i)=>`<path d="${v.rodada.map((r,j)=>`${j?"L":"M"}${ex(r).toFixed(1)} ${ey(v[key][j]).toFixed(1)}`).join("")}" fill="none" stroke="${pal[i]}" stroke-width="2.2"/><text x="${EW-er+6}" y="${ey(v[key][v[key].length-1])+4+(i%2?6:-2)}" font-size="11" fill="${pal[i]}">${esc(n)} ${pct(v[key][v[key].length-1])}</text>`).join("")}
   <text x="${(el+EW-er)/2}" y="${EH-4}" text-anchor="middle" font-size="10" fill="${col("--muted")}">rodada (antes de ser jogada)</text></svg><p class="note">Simulação do restante do campeonato antes de cada rodada, com as forças daquele momento e o calendário real. ${acS==="A"?"O Palmeiras foi o favorito da 1ª à 25ª rodada; o Flamengo assumiu antes da 26ª.":"Na Série B, sem histórico, o favorito trocou muitas vezes; o Novorizontino só se firmou na reta final."}</p>`;}
 // jogos
 const J=S.jogos,rounds=[...new Set(J.map(j=>j[0]))].sort((a,b)=>b-a);if(acR===null||!rounds.includes(acR))acR=rounds[0];
 $("ac-r").innerHTML=rounds.map(r=>`<option value="${r}"${r===acR?" selected":""}>${r}ª</option>`).join("");
 const O=["Mandante","Empate","Visitante"];
 $("ac-jogos").innerHTML=`<thead><tr><th class="l">Jogo</th><th>Casa · Empate · Fora</th><th>Palpite</th><th>Placar</th><th>Acertou</th></tr></thead><tbody>${J.filter(j=>j[0]===acR).map(j=>{const p=[j[5],j[6],j[7]],k=p.indexOf(Math.max(...p)),y=j[3]>j[4]?0:j[3]===j[4]?1:2;
  return`<tr><td class="l"><b>${esc(j[1])}</b> x ${esc(j[2])}</td><td class="num">${p.map((x,i)=>i===y?`<b>${pct(x)}</b>`:pct(x)).join(" · ")}</td><td class="num">${O[k]}</td><td class="num"><b>${j[3]} x ${j[4]}</b></td><td class="${k===y?"ok":"no"}">${k===y?"Sim":"Não"}</td></tr>`;}).join("")}</tbody>`;
 $("ac-note").textContent=acS==="A"?"Série A: Dixon-Coles de memória longa (o motor do portal), reajustado antes de cada rodada com toda a base de 2003 a 2025 e os jogos de 2026 já disputados. Jogos adiados foram previstos com o que se sabia antes da sua própria data. A chance em negrito é a do resultado que aconteceu.":"Série B: a base não tem jogos da Série B antes de 2026, então o modelo começou a temporada sem saber nada (na 1ª rodada, todos os clubes iguais) e foi aprendendo só com os jogos da própria Série B. Por isso o turno foi fraco e o returno, bem melhor.";}
document.addEventListener("click",e=>{const b=e.target.closest&&e.target.closest("button[data-ac]");if(!b)return;acS=b.dataset.ac;acR=null;b.parentElement.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",String(x===b)));renderAcerto();});
$("ac-r").addEventListener("change",e=>{acR=+e.target.value;renderAcerto();});

// ---------- Loteca ----------
// 14 jogos: os 10 da 32ª rodada da Série A e 4 da 35ª da Série B (exemplo; a grade oficial sai no concurso da Caixa)
// 14 jogos de exemplo: a próxima rodada da Série A e, para completar, a próxima da Série B (a grade oficial sai no concurso da Caixa)
const _SB=DATA.serieB,_nb=Math.min(..._SB.fixtures.map(f=>f.r));
const _la=FX.map((f,i)=>i).filter(i=>FX[i].r===NEXTA).slice(0,14),_lb=_SB.fixtures.map((f,i)=>i).filter(i=>_SB.fixtures[i].r===_nb).slice(0,14-_la.length);
const LOT=[..._la.map(k=>{const d=dA(FX[k].h,FX[k].a);return{hn:T(FX[k].h).name,an:T(FX[k].a).name,p:[d.W,d.D,d.L]};}),
 ..._lb.map(k=>{const f=_SB.fixtures[k],t=_SB.teams,P=_SB.params,d=dist(Math.exp(P.mu+P.home+t[f.h].att-t[f.a].dfn),Math.exp(P.mu+t[f.a].att-t[f.h].dfn),P.rho);return{hn:t[f.h].name,an:t[f.a].name,p:[d.W,d.D,d.L]};})];
const BUDGETS=[4,8,16,24,48,72,144,288,576,1728];
let budget=16,picks=null,custom=false;
const combosOf=pk=>pk.reduce((c,s)=>c*s.filter(Boolean).length,1);
function optimize(maxPrice){let best=null;
 for(let d=0;d<=9;d++)for(let t=0;t<=6;t++){const comb=Math.pow(2,d)*Math.pow(3,t);if(comb>864||d+t>14)continue;const price=Math.max(4,2*comb);if(price>maxPrice)continue;
  let dp=new Map([["0,0",{v:0,ch:[]}]]);
  for(let g=0;g<14;g++){const s=LOT[g].p.map((x,i)=>[x,i]).sort((a,b)=>b[0]-a[0]);const opts=[[0,0,Math.log(s[0][0])],[1,0,Math.log(s[0][0]+s[1][0])],[0,1,0]];
   const nd=new Map();for(const [k,st] of dp){const [cd,ct]=k.split(",").map(Number);for(const [od,ot,lv] of opts){const kd=cd+od,kt=ct+ot;if(kd>d||kt>t)continue;const key=kd+","+kt,val=st.v+lv,cur=nd.get(key);if(!cur||val>cur.v)nd.set(key,{v:val,ch:st.ch.concat([od?2:ot?3:1])});}}dp=nd;}
  const fin=dp.get(d+","+t);if(!fin)continue;if(!best||fin.v>best.v+1e-12||(Math.abs(fin.v-best.v)<1e-12&&price<best.price))best={v:fin.v,ch:fin.ch,price};}
 return best.ch.map((n,g)=>{const s=LOT[g].p.map((x,i)=>[x,i]).sort((a,b)=>b[0]-a[0]);const set=[false,false,false];for(let k=0;k<n;k++)set[s[k][1]]=true;return set;});}
function lotStats(pk){const cov=pk.map((s,g)=>s.reduce((a,on,i)=>a+(on?LOT[g].p[i]:0),0));const p14=cov.reduce((a,c)=>a*c,1);let p13=0;
 for(let i=0;i<14;i++){let pr=1-cov[i];for(let j=0;j<14;j++)if(j!==i)pr*=cov[j];p13+=pr;}
 const comb=combosOf(pk);let d=0,t=0;pk.forEach(s=>{const n=s.filter(Boolean).length;if(n===2)d++;if(n===3)t++;});return{cov,p14,p13:p13+p14,comb,price:Math.max(4,2*comb),d,t};}
function renderBudget(){$("budget").innerHTML=BUDGETS.map(b=>`<button type="button" class="pill" data-b="${b}" aria-pressed="${String(!custom&&b===budget)}">${brl(b).replace(",00","")}</button>`).join("");}
function renderVolante(){const st=lotStats(picks),O=["1","X","2"];
 $("volante").innerHTML=LOT.map((g,i)=>{const n=picks[i].filter(Boolean).length;
  return`<div class="vrow"><span class="n num">${i+1}</span><span class="h" title="${esc(g.hn)}">${esc(g.hn)}</span><div class="cells" role="group" aria-label="Jogo ${i+1}: ${esc(g.hn)} x ${esc(g.an)}">${O.map((o,k)=>`<button type="button" class="cell" data-g="${i}" data-k="${k}" aria-pressed="${picks[i][k]}" aria-label="${o==="X"?"Empate":o==="1"?esc(g.hn):esc(g.an)}, ${pct(g.p[k])}"><b>${o}</b><small class="num">${pct(g.p[k])}</small></button>`).join("")}</div><span class="a" title="${esc(g.an)}">${esc(g.an)}${n===2?'<span class="vtag d">Duplo</span>':n===3?'<span class="vtag t">Triplo</span>':""}</span><span class="cov num">${pct(st.cov[i])}</span></div>`;}).join("");
 $("p14").textContent=oneIn(st.p14);$("p14s").textContent=pct(st.p14)+" por volante";$("p13").textContent=oneIn(st.p13);$("p13s").textContent=pct(st.p13)+" por volante";
 $("price").textContent=brl(st.price);$("combos").textContent=`${nf0.format(st.comb)} combinaç${st.comb>1?"ões":"ão"}`;$("dt").textContent=`${st.d} · ${st.t}`;
 $("lotnote").innerHTML=st.comb>864?`<b>Passou do limite.</b> Um volante aceita até 864 combinações. Tire um duplo ou triplo.`:custom?`Volante personalizado. A sugestão do modelo para ${brl(budget)} tinha chance de ${oneIn(lotStats(optimize(budget)).p14)} de fazer 14.`:`Sugestão do modelo: a maior chance de 14 acertos que cabe em ${brl(budget)}. Duplos e triplos foram para os jogos mais equilibrados.`;
 $("voltext").value="Loteca · volante Oráculo (exemplo)\n"+LOT.map((g,i)=>`${String(i+1).padStart(2," ")}. ${g.hn} x ${g.an}: ${O.filter((o,k)=>picks[i][k]).join(" ")}`).join("\n")+`\nValor: ${brl(st.price)}`;}
function setBudget(b){budget=b;custom=false;picks=optimize(b);renderBudget();renderVolante();}
$("budget").addEventListener("click",e=>{const b=e.target.closest("button[data-b]");if(b)setBudget(+b.dataset.b);});
$("volante").addEventListener("click",e=>{const c=e.target.closest("button[data-g]");if(!c)return;const g=+c.dataset.g,k=+c.dataset.k,on=!picks[g][k];
 if(!on&&picks[g].filter(Boolean).length===1)return;picks[g][k]=on;custom=true;renderBudget();renderVolante();});
$("bestvol").addEventListener("click",()=>setBudget(budget));
function copyText(text,area,btn){const o=btn.textContent;const done=()=>{btn.textContent="Copiado";setTimeout(()=>btn.textContent=o,1600);};
 const fallback=()=>{if(area){area.hidden=false;area.value=text;area.focus();area.select();btn.textContent="Selecionado: use Ctrl+C";}};
 try{navigator.clipboard.writeText(text).then(done,fallback);}catch(err){fallback();}}
$("copyvol").addEventListener("click",e=>copyText($("voltext").value,$("voltext"),e.currentTarget));

// ---------- Série B: acesso direto, playoffs e rebaixamento ----------
const SB=DATA.serieB,BT=SB.teams,BP=SB.params,BFX=SB.fixtures,NB=BT.length;
const TB=i=>BT[i];
const dB=(h,a)=>dist(Math.exp(BP.mu+BP.home+BT[h].att-BT[a].dfn),Math.exp(BP.mu+BT[a].att-BT[h].dfn),BP.rho);
const NEXTB=Math.min(...BFX.map(f=>f.r)),BR35=BFX.map((f,i)=>i).filter(i=>BFX[i].r===NEXTB),BTRACK=BR35;
const fixedB={};let resB=null,prevSigB=null;
const OBJB=["acesso","rebaixamento"];
function simulateB(){
 const u=rng(4242),tit=new Float64Array(NB),dir=new Float64Array(NB),po=new Float64Array(NB),acc=new Float64Array(NB),z4=new Float64Array(NB),l6={},l16={};
 const A=new Float64Array(NB),Dm=new Float64Array(NB),P=new Float64Array(NB),V=new Float64Array(NB),SG=new Float64Array(NB),GP=new Float64Array(NB),tb=new Float64Array(NB);
 const idx=BT.map((t,i)=>i),outc=new Int8Array(BFX.length),Q=new Uint8Array(NB);
 const oc=BTRACK.map(()=>[0,0,0]),lv=BTRACK.map(()=>[0,1,2].map(()=>[[0,0],[0,0]]));
 const g=(x,y,home)=>poisson(Math.exp(BP.mu+(home?BP.home:0)+A[x]-Dm[y]),u);
 for(let s=0;s<SIMS;s++){
  for(let i=0;i<NB;i++){const t=BT[i];A[i]=t.att+BP.sigma*gauss(u);Dm[i]=t.dfn+BP.sigma*gauss(u);P[i]=t.pts;V[i]=t.v;SG[i]=t.gp-t.gc;GP[i]=t.gp;tb[i]=u();}
  for(let k=0;k<BFX.length;k++){const f=BFX[k],h=f.h,a=f.a;let gh,ga;
   if(fixedB[k]!==undefined){gh=fixedB[k]===2?0:1;ga=fixedB[k]===0?0:1;}else{gh=g(h,a,true);ga=g(a,h,false);}
   if(gh>ga){P[h]+=3;V[h]++;}else if(gh<ga){P[a]+=3;V[a]++;}else{P[h]++;P[a]++;}
   SG[h]+=gh-ga;SG[a]+=ga-gh;GP[h]+=gh;GP[a]+=ga;outc[k]=gh>ga?0:gh===ga?1:2;}
  idx.sort((x,y)=>P[y]-P[x]||V[y]-V[x]||SG[y]-SG[x]||GP[y]-GP[x]||tb[y]-tb[x]);
  const pos=new Int32Array(NB);for(let p=0;p<NB;p++)pos[idx[p]]=p;
  tit[idx[0]]++;dir[idx[0]]++;dir[idx[1]]++;for(let p=2;p<6;p++)po[idx[p]]++;for(let p=16;p<NB;p++)z4[idx[p]]++;
  l6[P[idx[5]]]=(l6[P[idx[5]]]||0)+1;l16[P[idx[15]]]=(l16[P[idx[15]]]||0)+1;
  // playoffs (regra CBF 2026): 3º x 6º e 4º x 5º; ida na casa do pior colocado, volta na do melhor; empate no agregado: avança a melhor campanha
  Q.fill(0);Q[idx[0]]=1;Q[idx[1]]=1;
  for(const [b,w] of [[idx[2],idx[5]],[idx[3],idx[4]]]){const wg=g(w,b,true)+g(w,b,false),bg=g(b,w,false)+g(b,w,true);Q[wg>bg?w:b]=1;}
  for(let i=0;i<NB;i++)acc[i]+=Q[i];
  for(let m=0;m<BTRACK.length;m++){const k=BTRACK[m],o=outc[k];oc[m][o]++;for(let sd=0;sd<2;sd++){const t=sd===0?BFX[k].h:BFX[k].a,L=lv[m][o][sd];if(Q[t])L[0]++;if(pos[t]>=16)L[1]++;}}}
 const prob=BT.map((t,i)=>({title:tit[i]/SIMS,dir:dir[i]/SIMS,po:po[i]/SIMS,acc:acc[i]/SIMS,z4:z4[i]/SIMS}));
 const levs=BTRACK.map((k,m)=>{if(fixedB[k]!==undefined)return null;let best=null;
  for(let sd=0;sd<2;sd++){const wi=sd===0?0:2,lo=sd===0?2:0;if(oc[m][wi]<300||oc[m][lo]<300)continue;
   for(let j=0;j<2;j++){const pw=lv[m][wi][sd][j]/oc[m][wi],pl=lv[m][lo][sd][j]/oc[m][lo],d=Math.abs(pw-pl);if(!best||d>best.d)best={d,team:sd===0?BFX[k].h:BFX[k].a,obj:OBJB[j],pw,pl};}}
  return best&&{k,...best};}).filter(Boolean).sort((a,b)=>b.d-a.d);
 const norm=o=>Object.entries(o).map(([p,c])=>[+p,c/SIMS]).sort((a,b)=>a[0]-b[0]);
 return{prob,levs,l6:norm(l6),l16:norm(l16)};}
function lineTxt(L){const top=L.slice().sort((a,b)=>b[1]-a[1])[0];let cum=0,med=L[0][0];for(const [p,c] of L){cum+=c;if(cum>=.5){med=p;break;}}
 const lo=L.find(x=>x[1]>=.02)[0],hi=L.filter(x=>x[1]>=.02).pop()[0];return{top,med,lo,hi};}
function renderB(){const pr=resB.prob,prev=prevSigB;
 $("btbody").innerHTML=BT.map((t,p)=>{const r=pr[p],gd=t.gp-t.gc;
  const zc=p<2?"var(--g6)":p<6?"var(--sula)":p>=16?"var(--z4)":"transparent";
  const cell=(x,c)=>`<td class="p c-${c}${x===0?" zero":""}"><i class="pb" style="--w:${(x*100).toFixed(1)}%"></i><span class="num">${pct(x)}</span></td>`;
  const ch=prev&&Math.abs(prev[p]-(r.acc+r.z4))>.02?' class="changed"':"";
  return`<tr${ch}><td class="pos num"><span class="z" style="background:${zc}"></span>${p+1}</td><td class="team">${esc(t.name)}</td><td class="pts num">${t.pts}</td><td class="num">${t.j}</td><td class="num">${gd>0?"+":""}${gd}</td>${cell(r.title,"title")}${cell(r.dir,"g6")}${cell(r.po,"sula")}${cell(r.acc,"g6")}${cell(r.z4,"z4")}</tr>`;}).join("");
 prevSigB=pr.map(r=>r.acc+r.z4);
 const a=lineTxt(resB.l6),b=lineTxt(resB.l16);
 $("blines").innerHTML=`<span class="lab">Linhas de corte projetadas:</span><div class="g"><b class="num">${a.med} pts</b><span>6º colocado, último do playoff (faixa ${a.lo}–${a.hi})</span></div><div class="g"><b class="num">${b.med} pts</b><span>16º colocado, primeiro fora da Z4 (faixa ${b.lo}–${b.hi})</span></div><span class="lab">Mediana das simulações; a faixa reúne as pontuações com ao menos 2% de chance.</span>`;
 const sorted=BT.map((t,i)=>({t,p:pr[i].acc})).sort((x,y)=>y.p-x.p).slice(0,6),mx=Math.max(sorted[0].p,.01);
 $("baccbars").innerHTML=sorted.map(o=>`<div class="tbar"><span>${esc(o.t.name)}</span><span class="track" role="img" aria-label="${esc(o.t.name)}: ${pct(o.p)}"><span class="fill" style="width:${(o.p/mx*100).toFixed(1)}%"></span></span><span class="v num">${pct(o.p)}</span></div>`).join("");}
function renderBFixtures(){$("bfixtures").innerHTML=BR35.map(k=>{const f=BFX[k],h=f.h,a=f.a,v=fixedB[k];
 const b=(val,txt)=>`<button type="button" data-mb="${k}" data-v="${val}" aria-pressed="${String(val==="auto"?v===undefined:v===val)}">${txt}</button>`;
 return`<div class="fxrow"><div class="fxhead"><span>${esc(TB(h).name)} x ${esc(TB(a).name)}</span><span class="muted">${esc(f.data)}</span></div>${wdlBar(TB(h).name,TB(a).name,TB(h).code,TB(a).code,dB(h,a))}<div class="seg" role="group" aria-label="Resultado de ${esc(TB(h).name)} x ${esc(TB(a).name)}">${b("auto","Modelo")}${b(0,TB(h).code)}${b(1,"Empate")}${b(2,TB(a).code)}</div></div>`;}).join("");}
function renderBracket(){const s=BT.map((t,i)=>i);const n=i=>esc(BT[s[i]].name);
 $("bracket").innerHTML=`<div class="fxrow"><div class="fxhead"><span>Se terminasse hoje</span><span class="muted">21 e 28/11</span></div>
  <div class="note"><b>3º ${n(2)}</b> x <b>6º ${n(5)}</b></div><div class="note"><b>4º ${n(3)}</b> x <b>5º ${n(4)}</b></div>
  <div class="note">Ida na casa do pior colocado, volta na casa do melhor. Empate no agregado: sobe quem fez a melhor campanha, sem pênaltis. ${n(0)} e ${n(1)} subiriam direto.</div></div>`;}
function runB(){$("bstatus").textContent="Simulando…";
 setTimeout(()=>{const t0=performance.now();resB=simulateB();const ms=Math.round(performance.now()-t0);renderB();renderGames();renderTiles();
  const nf=Object.keys(fixedB).length;$("bstatus").textContent=`${nf0.format(SIMS)} temporadas simuladas em ${ms} ms${nf?` · ${nf} escolha${nf>1?"s":""} sua${nf>1?"s":""}`:""}`;},20);}
$("bfixtures").addEventListener("click",e=>{const b=e.target.closest("button[data-mb]");if(!b)return;const k=+b.dataset.mb,v=b.dataset.v;if(v==="auto")delete fixedB[k];else fixedB[k]=+v;
 b.parentElement.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",String(x===b)));runB();});
$("brun").addEventListener("click",runB);
$("breset").addEventListener("click",()=>{for(const k in fixedB)delete fixedB[k];renderBFixtures();runB();});

// ---------- O modelo (resultados reais do backtest) ----------
const RES=DATA.res, MK=DATA.mk, ST=DATA.season, V2="Oráculo v2: empilhamento multiescala";
function renderModel(){const css=getComputedStyle(document.documentElement),col=v=>css.getPropertyValue(v).trim();
 const v2=RES[V2],m=MK["Mercado (casas de apostas)"];
 $("kpis").innerHTML=[["Acerto no 1X2",pct1(v2.acerto),`${nf0.format(v2.n)} jogos, 2017–2025`],["Dupla chance",pct1(v2.dupla),"acerto com os 2 resultados mais prováveis"],["Mercado, mesmos jogos",pct1(m.acerto),`${nf0.format(m.n)} jogos com odds`],
  ["Campeão após a 31ª",pct(ST["31"].fav),`${ST["31"].alta_ok} de ${ST["31"].alta} quando o favorito tinha ≥75%`],["Rebaixados após a 34ª",pct(ST["34"].z4),"dos clubes da Z4 previstos"]]
  .map(([k,v,s])=>`<div class="stat"><span class="k">${k}</span><span class="v num">${v}</span><span class="s">${s}</span></div>`).join("");
 const mk=DATA.market,pick=["Todas as ligas (2000–2026)","Brasil Série A (2012–2024)","Serie A Itália","Premier League","La Liga","Argentina"];
 const rows=pick.map(n=>mk.find(r=>r.grupo===n)).filter(Boolean).map(r=>({n:"Mercado · "+r.grupo,a:r.acerto,us:false}));
 rows.push({n:"Oráculo v2 · Brasileirão 2017–2025",a:v2.acerto,us:true});
 $("ceil").innerHTML=rows.map(r=>`<div class="r${r.us?" us":""}"><span>${esc(r.n)}</span><span class="t"><i style="width:${r.a*100}%"></i></span><span class="v num">${pct1(r.a)}</span></div>`).join("")+`<div class="r"><span><b>Meta pedida</b></span><span class="t" style="background:transparent;border:1px dashed var(--loss)"><i style="width:85%;background:transparent"></i></span><span class="v num">85%</span></div>`;
 const ms=DATA.market_sel.find(r=>r.limiar===0.8),sl=DATA.sel.find(r=>r.limiar===0.7);
 $("where85").innerHTML=`<thead><tr><th class="l">Recorte</th><th>Casos</th><th>Acerto</th></tr></thead><tbody>
  <tr><td class="l">Favorito ao título com ≥75%, após a 31ª rodada</td><td class="num">${ST["31"].alta} temporadas</td><td class="num ok">${pct(ST["31"].alta_ok/ST["31"].alta)}</td></tr>
  <tr><td class="l">Favorito do mercado com ≥80% num jogo</td><td class="num">${pct1(ms.cobertura)} dos jogos</td><td class="num ok">${pct1(ms.acerto)}</td></tr>
  <tr><td class="l">Rebaixados previstos após a 34ª rodada</td><td class="num">80 clubes</td><td class="num">${pct(ST["34"].z4)}</td></tr>
  <tr><td class="l">Dupla chance em todos os jogos</td><td class="num">${nf0.format(v2.n)} jogos</td><td class="num">${pct1(v2.dupla)}</td></tr>
  <tr><td class="l">Oráculo com ≥70% num jogo</td><td class="num">${sl?sl.jogos:"—"} jogos</td><td class="num">${sl?pct1(sl.acerto):"—"}</td></tr></tbody>`;
 // memória
 const hl=DATA.halflife,W=520,H=230,L=56,Rr=16,Tp=14,Bt=40,lo=Math.min(...hl.map(r=>r.rps))-.0004,hi=Math.max(...hl.map(r=>r.rps))+.0004;
 const lx=v=>Math.log(v),X=v=>L+(lx(v)-lx(hl[0].half_life))/(lx(hl[hl.length-1].half_life)-lx(hl[0].half_life))*(W-L-Rr),Y=v=>Tp+(hi-v)/(hi-lo)*(H-Tp-Bt);
 const ticks=[];for(let v=Math.ceil(lo*1000)/1000;v<=hi;v+=.001)ticks.push(v);
 const lbl={45:"45 d",90:"3 m",180:"6 m",365:"1 ano",730:"2 anos",1095:"3 anos"};
 const bestH=hl.reduce((a,b)=>b.rps<a.rps?b:a);
 $("hlchart").innerHTML=`<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Erro do modelo por tamanho da memória: cai de 45 dias até cerca de 2 anos e estabiliza">
  ${ticks.map(v=>`<line x1="${L}" x2="${W-Rr}" y1="${Y(v)}" y2="${Y(v)}" stroke="${col("--line")}"/><text x="${L-8}" y="${Y(v)+4}" text-anchor="end" font-size="11" fill="${col("--muted")}" font-family="IBM Plex Mono, monospace">${nf3.format(v)}</text>`).join("")}
  ${hl.filter(r=>lbl[r.half_life]).map(r=>`<text x="${X(r.half_life)}" y="${H-18}" text-anchor="middle" font-size="11" fill="${col("--muted")}">${lbl[r.half_life]}</text>`).join("")}
  <text x="${(L+W-Rr)/2}" y="${H-2}" text-anchor="middle" font-size="11" fill="${col("--muted")}">meia-vida da memória do modelo (escala log)</text>
  <path d="${hl.map((r,i)=>`${i?"L":"M"}${X(r.half_life).toFixed(1)} ${Y(r.rps).toFixed(1)}`).join("")}" fill="none" stroke="${col("--pitch")}" stroke-width="2.5"/>
  ${hl.map(r=>`<circle cx="${X(r.half_life)}" cy="${Y(r.rps)}" r="${r===bestH?5:3}" fill="${r===bestH?col("--canarinho"):col("--pitch")}"/>`).join("")}
  <text x="${X(hl[0].half_life)+6}" y="${Y(hl[0].rps)-8}" font-size="12" fill="${col("--ink")}">só o momento: erra mais</text>
 </svg><p class="note">RPS médio na validação (2008–2016), quanto menor melhor. Com chutes no alvo, 6 meses de memória chegam ao mesmo erro de 2 anos só com gols.</p>`;
 // calibração
 const cal=DATA.cal,CW=360,CH=260,cl=44,cb=34,ct=10,cr=12,cx=v=>cl+v*(CW-cl-cr),cy=v=>ct+(1-v)*(CH-ct-cb);
 $("calchart").innerHTML=`<svg viewBox="0 0 ${CW} ${CH}" role="img" aria-label="Probabilidade prevista contra frequência observada: os pontos ficam sobre a diagonal">
  ${[0,.2,.4,.6,.8].map(v=>`<line x1="${cl}" x2="${CW-cr}" y1="${cy(v)}" y2="${cy(v)}" stroke="${col("--line")}"/><text x="${cl-6}" y="${cy(v)+4}" text-anchor="end" font-size="11" fill="${col("--muted")}" font-family="IBM Plex Mono, monospace">${v*100}%</text><text x="${cx(v)}" y="${CH-cb+16}" text-anchor="middle" font-size="11" fill="${col("--muted")}" font-family="IBM Plex Mono, monospace">${v*100}%</text>`).join("")}
  <line x1="${cx(0)}" y1="${cy(0)}" x2="${cx(.8)}" y2="${cy(.8)}" stroke="${col("--muted")}" stroke-dasharray="4 4"/>
  ${cal.map(r=>`<circle cx="${cx(r.previsto)}" cy="${cy(r.observado)}" r="${3+Math.sqrt(r.n)/12}" fill="${col("--pitch")}" fill-opacity=".75"/>`).join("")}
  <text x="${(cl+CW-cr)/2}" y="${CH-2}" text-anchor="middle" font-size="11" fill="${col("--muted")}">probabilidade prevista</text>
 </svg><p class="note">Cada ponto é uma faixa de 10 pontos percentuais; o tamanho mostra quantas previsões caíram nela. A linha tracejada é a calibração perfeita.</p>`;
 // comparação
 const cmpRows=[...Object.entries(RES).map(([k,r])=>({k,r,us:k===V2})),...Object.entries(MK).map(([k,r])=>({k:k+(k.startsWith("Oráculo")?" (jogos com odds)":" (jogos com odds)"),r,us:false}))];
 $("cmp").innerHTML=`<thead><tr><th class="l">Modelo</th><th>Jogos</th><th>Acerto</th><th>Dupla chance</th><th>RPS</th><th>Log loss</th></tr></thead><tbody>${cmpRows.map(({k,r,us})=>`<tr${us?' style="background:color-mix(in srgb,var(--canarinho) 14%,transparent)"':""}><td class="l">${esc(k)}</td><td class="num">${nf0.format(r.n)}</td><td class="num">${pct1(r.acerto)}</td><td class="num">${pct1(r.dupla)}</td><td class="num">${nf3.format(r.rps)}</td><td class="num">${nf3.format(r.logloss)}</td></tr>`).join("")}</tbody>`;
 $("seasons").innerHTML=`<thead><tr><th>Ano</th><th class="l">Campeão</th><th class="l">Favorito do modelo</th><th>Chance do favorito</th><th>Acertou</th><th>Z4 prevista</th></tr></thead><tbody>${DATA.s31.map(r=>`<tr><td class="num">${r.temporada}</td><td class="l">${esc(r.campeao)}</td><td class="l">${esc(r.favorito)}</td><td class="num">${pct(r.p_fav)}</td><td class="${r.acertou_campeao?"ok":"no"}">${r.acertou_campeao?"Sim":"Não"}</td><td class="num">${r.z4_acertos} de 4</td></tr>`).join("")}</tbody>`;
 renderCalib();renderStats();lab();}
function renderCalib(){const C=DATA.calib_temporada;if(!C)return;const rows=[["Série A, parâmetros antigos (K = 12, σ = 0,07)",C.antigo],[`Série A, v2.3 (K = ${nf0.format(C.blend.K)}, σ = ${nf2.format(C.blend.sigma)})`,C.blend],[`Só a temporada, método da Série B (K = ${nf0.format(C.agg.K)}, σ = ${nf2.format(C.agg.sigma)})`,C.agg]];
 $("calib").innerHTML=`<thead><tr><th class="l">Método</th><th>Rodada</th><th>Campeão certo</th><th>G4 certos</th><th>Z4 certos</th><th>Log loss do título</th></tr></thead><tbody>${rows.map(([n,c],j)=>c.prova.map((r,i)=>`<tr${j===1?' style="background:color-mix(in srgb,var(--canarinho) 14%,transparent)"':""}>${i===0?`<td class="l" rowspan="${c.prova.length}">${esc(n)}</td>`:""}<td class="num">${r.rodada}ª</td><td class="num">${pct(r.acerto_tit)}</td><td class="num">${pct(r.acerto_g4)}</td><td class="num">${pct(r.acerto_z4)}</td><td class="num">${nf3.format(r.ll_tit)}</td></tr>`).join("")).join("")}</tbody>`;}
const NAMEV={"longo_lr":"Força Poisson (memória longa)","elo":"Elo","longo_la":"Gols esperados do visitante (memória longa)","chutes_lr":"Força Poisson com chutes","longo_pD":"Chance de empate (memória longa)","chutes_lh":"Gols esperados do mandante (chutes)","d_pos":"Diferença de posição na tabela","curto_lr":"Força Poisson (memória curta)","longo_lh":"Gols esperados do mandante (memória longa)","d_pts5":"Diferença de pontos nos últimos 5 jogos","h_ga10":"Gols sofridos pelo mandante (10 jogos)","h_ppg":"Pontos por jogo do mandante na temporada","curto_la":"Gols esperados do visitante (memória curta)","chutes_la":"Gols esperados do visitante (chutes)","a_pts10":"Pontos do visitante (10 jogos)"};
function renderStats(){const S=DATA.stats;if(!S)return;
 $("stbl").innerHTML=`<thead><tr><th class="l">Modelo</th><th>Acerto (IC 95%)</th><th>RPS</th><th>Diferença de RPS vs v2 (IC 95%)</th><th>p</th></tr></thead><tbody>${S.modelos.map(r=>`<tr><td class="l">${esc(r.modelo)}</td><td class="num">${pct1(r.acerto)} (${pct1(r.ic_lo)}–${pct1(r.ic_hi)})</td><td class="num">${nf4.format(r.rps)}</td><td class="num">${r.dif_rps_vs_v2==null?"—":`${r.dif_rps_vs_v2>0?"+":""}${nf4.format(r.dif_rps_vs_v2)} (${nf4.format(r.ic_dif_lo)} a ${nf4.format(r.ic_dif_hi)})`}</td><td class="num ${r.p_dm!=null&&r.p_dm<.05?"ok":""}">${r.p_dm==null?"—":r.p_dm<.001?"&lt;0,001":nf3.format(r.p_dm)}</td></tr>`).join("")}
  <tr><td class="l">Mercado de apostas (${nf0.format(S.mercado.jogos)} jogos)</td><td class="num">${pct1(S.mercado.acerto_mercado)}</td><td class="num">—</td><td class="num">${nf4.format(-S.mercado.dif_rps)} (${nf4.format(-S.mercado.ic[1])} a ${nf4.format(-S.mercado.ic[0])})</td><td class="num ok">${S.mercado.p_dm<.001?"&lt;0,001":nf3.format(S.mercado.p_dm)}</td></tr></tbody>`;
 $("stnote").textContent=`Empates foram ${pct1(S.empates_reais)} dos jogos, mas o empate foi o resultado mais provável em só ${pct1(S.empate_favorito)} das previsões. Por isso um palpite único não passa de cerca de ${pct(1-S.empates_reais)} de acerto, nem em teoria. Modelo e mercado apontaram o mesmo favorito em ${pct(S.mercado.concordancia_favorito)} dos jogos.`;
 const ML=DATA.ml_full,rows=[["Só variáveis brutas (logística)","lr:so_bruto"],["Só variáveis brutas (boosting)","gb:so_bruto"],["Todas as variáveis (logística)","lr:tudo"],["Todas as variáveis (boosting)","gb:tudo"],["Oráculo v2 (referência)","v2 (referência)"]];
 $("mltbl").innerHTML=`<thead><tr><th class="l">Modelo</th><th>Acerto</th><th>RPS</th></tr></thead><tbody>${rows.filter(([n,k])=>ML[k]).map(([n,k])=>`<tr${k.startsWith("v2")?' style="background:color-mix(in srgb,var(--canarinho) 14%,transparent)"':""}><td class="l">${n}</td><td class="num">${pct1(ML[k].acerto)}</td><td class="num">${nf4.format(ML[k].rps)}</td></tr>`).join("")}</tbody>`;
 const I=DATA.importancia||[],mx=Math.max(...I.map(x=>x.i));
 $("imp").innerHTML=I.slice(0,10).map(x=>`<div class="ceil"><div class="r" style="grid-template-columns:minmax(0,1fr) 120px"><span style="font-size:13px">${esc(NAMEV[x.v]||x.v)}</span><span class="t"><i style="width:${Math.max(2,x.i/mx*100)}%"></i></span></div></div>`).join("");}

// ---------- Base de dados ----------
let BASEJ=null;
function loadBase(){if(BASEJ){renderBase();return;}
 $("b-note").textContent="Carregando os jogos…";
 fetch(ROOT+"data/jogos.json").then(r=>{if(!r.ok)throw new Error(r.status);return r.json();}).then(j=>{BASEJ=j;
  const seasons=[...new Set(j.historico.map(r=>r[1]))].sort((a,b)=>b-a);
  $("b-season").innerHTML=`<option value="2026">2026 (até 04/11)</option>`+seasons.map(s=>`<option value="${s}">${s}</option>`).join("");
  renderBase();}).catch(()=>{$("b-note").textContent="Não foi possível carregar data/jogos.json. Recarregue a página para tentar de novo.";});}
function renderBase(){if(!BASEJ)return;const s=+$("b-season").value||2026,q=$("b-team").value.trim().toLowerCase();
 const src=s===2026?BASEJ.t2026:BASEJ.historico.filter(r=>r[1]===s);
 const all=src, rows=q?src.filter(r=>r[3].toLowerCase().includes(q)||r[4].toLowerCase().includes(q)):src;
 const n=all.length,hw=all.filter(r=>r[5]>r[6]).length,dr=all.filter(r=>r[5]===r[6]).length,gl=all.reduce((a,r)=>a+r[5]+r[6],0);
 $("b-kpis").innerHTML=[["Jogos",nf0.format(n),s===2026?"2026 até 04/11":"temporada completa"],["Vitória do mandante",pct(hw/n),""],["Empates",pct(dr/n),""],["Vitória do visitante",pct((n-hw-dr)/n),""],["Gols por jogo",nf2.format(gl/n),""]]
  .map(([k,v,x])=>`<div class="stat"><span class="k">${k}</span><span class="v num">${v}</span><span class="s">${x}</span></div>`).join("");
 const show=rows.slice().reverse().slice(0,400);
 $("b-tbl").innerHTML=`<thead><tr><th class="l">Data</th><th>Rodada</th><th class="l">Mandante</th><th>Placar</th><th class="l">Visitante</th></tr></thead><tbody>${show.map(r=>`<tr><td class="l num">${r[0].split("-").reverse().join("/")}</td><td class="num">${r[2]??"—"}</td><td class="l">${esc(r[3])}</td><td class="num"><b>${r[5]} x ${r[6]}</b></td><td class="l">${esc(r[4])}</td></tr>`).join("")}</tbody>`;
 $("b-note").textContent=`${nf0.format(rows.length)} jogo${rows.length===1?"":"s"}${q?` com "${$("b-team").value.trim()}"`:""}${rows.length>400?"; mostrando os 400 mais recentes":""}. Nomes como na base original (sem acentos até 2025).`;}
$("b-season").addEventListener("change",renderBase);$("b-team").addEventListener("input",renderBase);

// ---------- Laboratório (3.420 jogos reais) ----------
const LAB=DATA.lab;
const rps=(p,o)=>{const e=[0,0,0];e[o]=1;return .5*((p[0]-e[0])**2+((p[0]+p[1])-(e[0]+e[1]))**2);};
function evalLab(dh,rho){let s=0,hit=0;for(const [lh,la,o] of LAB){const d=dist(lh*Math.exp(dh),la,rho),p=[d.W,d.D,d.L];s+=rps(p,o);if(p.indexOf(Math.max(...p))===o)hit++;}return{rps:s/LAB.length,hit};}
let BASE=null,labT=null;
function lab(){const dh=+$("s-home").value,rho=+$("s-rho").value;$("v-home").textContent=(dh>0?"+":"")+nf2.format(dh);$("v-rho").textContent=nf2.format(rho);
 clearTimeout(labT);labT=setTimeout(()=>{if(!BASE)BASE=evalLab(0,RHO);const B=evalLab(dh,rho),d=B.rps-BASE.rps;
  $("labout").innerHTML=`RPS ${nf3.format(B.rps)} (modelo ${nf3.format(BASE.rps)}) · ${B.hit} acertos em ${nf0.format(LAB.length)} (${pct1(B.hit/LAB.length)})<br>${d<-1e-5?"<b>Errou menos.</b> No ciclo semanal, este desafiante ainda precisaria vencer nas últimas oito semanas para virar o modelo oficial.":d>1e-5?"<b>Errou mais.</b> O desafiante perderia e o modelo atual seria mantido.":"Igual ao modelo atual: nada mudaria."}`;},60);}
$("s-home").value=0;$("s-rho").value=RHO;
$("s-home").addEventListener("input",lab);$("s-rho").addEventListener("input",lab);
$("labreset").addEventListener("click",()=>{$("s-home").value=0;$("s-rho").value=RHO;lab();});

// ---------- atualização semanal e painel ----------
function nextMonday(){const d=new Date();let add=(8-d.getDay())%7;if(add===0&&d.getHours()>=6)add=7;return new Date(d.getFullYear(),d.getMonth(),d.getDate()+add,6,0,0);}
const NM=nextMonday(),nmTxt=NM.toLocaleDateString("pt-BR",{day:"2-digit",month:"2-digit"});
$("cl-next").textContent=NM.toLocaleDateString("pt-BR");
function renderTiles(){if(!result||!resB||!picks)return;const top=allLevs()[0],st=lotStats(optimize(16)),v2=RES[V2],m=MK["Mercado (casas de apostas)"];
 const hrs=Math.max(0,Math.round((NM-new Date())/36e5)),dd=Math.floor(hrs/24),hh=hrs%24;
 const tf=top&&(top.lg==="A"?FX[top.k]:BFX[top.k]),TT=top&&(top.lg==="A"?T:TB);
 const bAcc=BT.map((t,i)=>({t,p:resB.prob[i].acc})).sort((a,b)=>b.p-a.p)[0];
 const tiles=[
  {href:ROOT+"jogos-da-semana/",k:"Jogo mais decisivo",big:top?`${TT(tf.h).code} x ${TT(tf.a).code}`:"—",p:top?`Série ${top.lg}: muda em ${nf0.format(top.d*100)} p.p. a chance de ${top.obj} de ${TT(top.team).name}`:"Todos os jogos estão fixados",go:"Ver jogos"},
  {href:ROOT+"serie-b/",k:"Favorito ao acesso",big:pct(bAcc.p),p:`${bAcc.t.name}, somando acesso direto e playoffs da Série B`,go:"Ver Série B"},
  {href:ROOT+"acerto-2026/",k:"Acerto em 2026",big:DATA.bt2026?pct1(DATA.bt2026.A.acerto):"—",p:DATA.bt2026?`Palpites da Série A desde a 1ª rodada, só com o passado. Sempre o mandante: ${pct1(DATA.bt2026.A.ref_mandante)}.`:"",go:"Ver rodada a rodada"},
  {href:ROOT+"loteca/",k:"Loteca da semana",big:oneIn(st.p14),p:"Chance de 14 acertos com o volante sugerido de R$ 16",go:"Montar volante"}];
 $("tiles").innerHTML=tiles.map(t=>`<a class="tile" href="${t.href}"><span class="eyebrow">${t.k}</span><span class="big num">${t.big}</span><p>${t.p}</p><span class="go">${t.go} →</span></a>`).join("");}

// ---------- navegação ----------
const VIEWS=["inicio", "brasileirao", "serieb", "copa-do-brasil", "libertadores", "sul-americana", "acerto", "jogos", "rankings", "loteca", "modelo", "base"];
function drawPitch(c){const r=c.getBoundingClientRect();if(!r.width)return;const d=window.devicePixelRatio||1;c.width=r.width*d;c.height=r.height*d;
 const g=c.getContext("2d");g.scale(d,d);const W=r.width,H=r.height,cs=getComputedStyle(document.documentElement);
 g.clearRect(0,0,W,H);for(let x=0;x<W;x+=90){g.fillStyle=(x/90)%2?"rgba(255,255,255,0.025)":"rgba(0,0,0,0.05)";g.fillRect(x,0,90,H);}
 g.strokeStyle=cs.getPropertyValue("--chalk-line").trim()||"rgba(255,255,255,.15)";g.lineWidth=2;const cx=W*.8,cy=H*.5;
 g.beginPath();g.arc(cx,cy,Math.min(H*.42,170),0,Math.PI*2);g.stroke();g.beginPath();g.moveTo(cx,0);g.lineTo(cx,H);g.stroke();
 g.beginPath();g.arc(cx,cy,4,0,Math.PI*2);g.fillStyle=g.strokeStyle;g.fill();g.strokeRect(W-110,cy-150,140,300);}
let modelDone=false;
function show(v,scroll){if(!VIEWS.includes(v))v="inicio";
 document.querySelectorAll(".view").forEach(s=>s.hidden=s.dataset.view!==v);

 const cur=document.querySelector("#nav a[aria-current]");if(cur&&cur.scrollIntoView)try{cur.scrollIntoView({block:"nearest",inline:"nearest"});}catch(e){}
 document.querySelectorAll(`.view[data-view="${v}"] canvas.pitch`).forEach(drawPitch);
 if(v==="modelo"&&!modelDone){modelDone=true;renderModel();}
 if(v==="base")loadBase();
 if(v==="acerto")renderAcerto();
}

window.addEventListener("resize",()=>document.querySelectorAll(".view:not([hidden]) canvas.pitch").forEach(drawPitch));

renderFixtures();renderBFixtures();renderBracket();renderRank();setBudget(16);
show(PAGE,false);
run();runB();
}
// O portal lê os dados publicados junto com ele; a cópia embutida é reserva.
fetch(ROOT+"data/portal.json",{cache:"no-cache"}).then(r=>{if(!r.ok)throw new Error(r.status);return r.json();}).then(boot).catch(e=>{console.error(e);const m=document.querySelector("main");if(m)m.insertAdjacentHTML("afterbegin",`<p class="wrap" style="padding:24px 16px">Não foi possível carregar os dados. Recarregue a página.</p>`);});
})();
