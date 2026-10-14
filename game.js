const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');
const W = canvas.width, H = canvas.height;
const TILE = 40, COLS = 20, ROWS = 15;

const levelEl = document.getElementById('level');
const scoreEl = document.getElementById('score');
const gemsEl = document.getElementById('gems');
const healthFill = document.getElementById('healthFill');
const overlay = document.getElementById('overlay');
const gameOver = document.getElementById('gameOver');
const startBtn = document.getElementById('startBtn');
const retryBtn = document.getElementById('retryBtn');
const soundBtn = document.getElementById('soundBtn');
const overlayTitle = document.getElementById('overlayTitle');
const overlayText = document.getElementById('overlayText');
const finalScore = document.getElementById('finalScore');
const finalLevel = document.getElementById('finalLevel');

// ===== STATE =====
let gameState = 'menu'; // menu | playing | paused | gameover
let grid = [];
let player, monsters, particles, gemsCount;
let score, level, health, maxHealth;
let keys = {};
let lastDir = { x: 1, y: 0 };
let mouse = { x: -100, y: -100 };
let attackCooldown = 0;
let playerInvuln = 0;
let message = '';
let messageTimer = 0;
let paused = false;
let audioCtx = null;
let soundOn = true;
let lastTime = 0;
let shake = 0;

function ensureAudio(){ if(!audioCtx){ try{audioCtx=new (window.AudioContext||window.webkitAudioContext)();}catch(e){audioCtx=null;} } return audioCtx; }
function beep(freq,dur,type='square',vol=0.07){ if(!soundOn) return; const c=ensureAudio(); if(!c) return; try{ const o=c.createOscillator(),g=c.createGain(); o.type=type; o.frequency.value=freq; g.gain.setValueAtTime(vol,c.currentTime); g.gain.exponentialRampToValueAtTime(0.0001,c.currentTime+dur); o.connect(g).connect(c.destination); o.start(); o.stop(c.currentTime+dur);}catch(e){} }

function rnd(a,b){ return Math.floor(Math.random()*(b-a+1))+a; }
function clamp(v,min,max){ return Math.max(min,Math.min(max,v)); }

// ===== MAP GENERATION =====
function emptyTiles() {
  const out=[];
  for (let y=1;y<ROWS-1;y++) for (let x=1;x<COLS-1;x++) {
    if (grid[y][x] === 0) out.push({x,y});
  }
  return out;
}
function bfs(start, goal) {
  const key = p => `${p.x},${p.y}`;
  const q = [start];
  const visited = new Set([key(start)]);
  const parent = new Map();
  while (q.length) {
    const cur = q.shift();
    if (cur.x===goal.x && cur.y===goal.y) {
      const path=[cur]; let p=parent.get(key(cur));
      while(p){ path.unshift(p); p=parent.get(key(p)); }
      return path;
    }
    const dirs=[[1,0],[-1,0],[0,1],[0,-1]];
    for (const d of dirs) {
      const nx=cur.x+d[0], ny=cur.y+d[1];
      if (ny<0||ny>=ROWS||nx<0||nx>=COLS) continue;
      if (grid[ny][nx]===1) continue;
      const nk=`${nx},${ny}`;
      if (visited.has(nk)) continue;
      visited.add(nk);
      parent.set(nk, cur);
      q.push({x:nx,y:ny});
    }
  }
  return null;
}
function generateLevel(lvl) {
  grid = Array.from({length:ROWS}, ()=>Array(COLS).fill(0));
  // borders
  for (let x=0;x<COLS;x++){ grid[0][x]=1; grid[ROWS-1][x]=1; }
  for (let y=0;y<ROWS;y++){ grid[y][0]=1; grid[y][COLS-1]=1; }
  // corridor guarantee: top row path + right column down
  for (let x=1;x<COLS-1;x++) grid[1][x]=0;
  for (let y=1;y<ROWS-1;y++) grid[y][COLS-2]=0;
  // random walls
  for (let y=2;y<ROWS-2;y++) for (let x=2;x<COLS-3;x++) {
    if (Math.random() < 0.20) grid[y][x]=1;
  }
  // clear start/exit neighborhood
  for (let y=1;y<=2;y++) for (let x=1;x<=2;x++) grid[y][x]=0;
  grid[ROWS-2][COLS-2]=2; // exit
  for (let y=ROWS-3;y<=ROWS-2;y++) for (let x=COLS-3;x<=COLS-2;x++) if(grid[y][x]===1) grid[y][x]=0;

  // gems
  const et = emptyTiles().filter(t=>!(t.x<=2&&t.y<=2) && !(t.x>=COLS-3&&t.y>=ROWS-3));
  const gemCount = 3 + lvl;
  for (let i=0;i<gemCount && et.length;i++){
    const idx = Math.floor(Math.random()*et.length);
    const t = et.splice(idx,1)[0];
    grid[t.y][t.x] = 3;
  }
  // monsters
  const candidates = et.filter(t=> (t.x>3||t.y>3));
  const monsterCount = Math.min(candidates.length, 2 + lvl);
  const picks = [...candidates].sort(()=>Math.random()-0.5).slice(0, monsterCount);
  monsters = picks.map((t, idx) => ({
    x: (t.x+0.5)*TILE, y: (t.y+0.5)*TILE,
    tx: t.x, ty: t.y,
    type: idx % 2 === 0 ? 'slime' : 'demon',
    speed: (idx%2===0 ? 48 : 78) + lvl*10,
    hp: 1,
    actTimer: 0.4 + Math.random()*0.4,
    nextTile: null,
    flash: 0
  }));
  player.x = 1.5*TILE; player.y = 1.5*TILE;
  player.invuln = 1;
}

// ===== COLLISION =====
function tileAt(px, py) {
  const tx = Math.floor(px / TILE), ty = Math.floor(py / TILE);
  if (ty<0||ty>=ROWS||tx<0||tx>=COLS) return 1;
  return grid[ty][tx];
}
function walkable(tx,ty){ return tx>=0&&ty>=0&&tx<COLS&&ty<ROWS && grid[ty][tx]!==1; }
function canMove(px,py,r) {
  const pts=[[px-r,py-r],[px+r,py-r],[px-r,py+r],[px+r,py+r]];
  for (const [x,y] of pts) { if (tileAt(x,y)===1) return false; }
  return true;
}

// ===== INIT =====
function resetGame() {
  score=0; level=1; gemsCount=0; health=3; maxHealth=3;
  monsters=[]; particles=[];
  player = { x:1.5*TILE, y:1.5*TILE, r:12, speed:150, vx:0, vy:0, dirX:1, dirY:0, attackCd:0 };
  generateLevel(level);
  gameState='playing';
  overlay.hidden=true; gameOver.hidden=true;
  message='Nivel 1: busca la salida.'; messageTimer=2.5;
  updateHud();
}

function nextLevel() {
  level++;
  health = Math.min(maxHealth, health+1);
  monsters=[]; particles=[];
  generateLevel(level);
  player.x=1.5*TILE; player.y=1.5*TILE; player.invuln=1; attackCooldown=0;
  message = `¡Nivel ${level}!`; messageTimer=2;
  updateHud();
  beep(700,0.12,'triangle',0.08); setTimeout(()=>beep(900,0.15,'triangle',0.08),120);
}

function gameOverState() {
  gameState='gameover';
  finalScore.textContent=score; finalLevel.textContent=level;
  gameOver.hidden=false;
  beep(90,0.5,'sawtooth',0.12);
}

function updateHud() {
  levelEl.textContent=level;
  scoreEl.textContent=score;
  gemsEl.textContent=gemsCount;
  healthFill.style.width = (health/maxHealth*100)+'%';
}

function makeParticle(x,y,color) {
  particles.push({x,y,vx:(Math.random()-0.5)*120,vy:(Math.random()-0.5)*120,life:0.4,max:0.4,color,r:Math.random()*3+1});
}

// ===== UPDATE =====
function update(dt) {
  if (gameState!=='playing') return;
  if (paused) return;

  // player input
  let vx=0,vy=0;
  if (keys['ArrowUp']||keys['KeyW']) vy=-1;
  if (keys['ArrowDown']||keys['KeyS']) vy=1;
  if (keys['ArrowLeft']||keys['KeyA']) vx=-1;
  if (keys['ArrowRight']||keys['KeyD']) vx=1;
  const len = Math.hypot(vx,vy);
  if (len>0){ vx/=len; vy/=len; lastDir={x:vx,y:vy}; }
  player.vx = vx*player.speed;
  player.vy = vy*player.speed;
  // move
  let nx = player.x + player.vx*dt;
  if (canMove(nx, player.y, player.r)) player.x = nx;
  let ny = player.y + player.vy*dt;
  if (canMove(player.x, ny, player.r)) player.y = ny;
  player.x = clamp(player.x, player.r, W-player.r);
  player.y = clamp(player.y, player.r, H-player.r);
  if (player.attackCd>0) player.attackCd -= dt;
  if (player.invuln>0) player.invuln -= dt;

  // attack
  if (keys['Space'] && player.attackCd<=0) {
    keys['Space']=false;
    player.attackCd=0.3;
    // target tile in front
    const tx = Math.floor(player.x/TILE)+Math.round(lastDir.x);
    const ty = Math.floor(player.y/TILE)+Math.round(lastDir.y);
    let hit=false;
    for (let i=monsters.length-1;i>=0;i--){
      const m=monsters[i];
      const mt={x:Math.floor(m.x/TILE), y:Math.floor(m.y/TILE)};
      if (mt.x===tx && mt.y===ty) {
        monsters.splice(i,1);
        score += 10;
        for (let k=0;k<8;k++) makeParticle(m.x,m.y,'#ef4444');
        beep(300,0.1,'square',0.06);
        hit=true;
      }
    }
    if (!hit) beep(180,0.05,'square',0.03);
    updateHud();
  }

  // gems collection
  const ptx=Math.floor(player.x/TILE), pty=Math.floor(player.y/TILE);
  if (grid[pty] && grid[pty][ptx]===3) {
    grid[pty][ptx]=0;
    gemsCount++; score += 5;
    for (let k=0;k<6;k++) makeParticle(player.x,player.y,'#fbbf24');
    beep(600,0.08,'triangle',0.06);
    updateHud();
  }
  // next level?
  if (grid[pty] && grid[pty][ptx]===2) {
    nextLevel();
  }

  // monsters AI + movement
  const playerTile = {x:Math.floor(player.x/TILE), y:Math.floor(player.y/TILE)};
  for (const m of monsters) {
    m.actTimer -= dt;
    if (m.actTimer <= 0) {
      // choose target
      let target = null;
      const d = Math.hypot(m.x-player.x, m.y-player.y);
      if (m.type==='demon' || d < 220) target = playerTile;
      else {
        // wander
        const dirs=[[1,0],[-1,0],[0,1],[0,-1]].sort(()=>Math.random()-0.5);
        for (const dd of dirs) {
          const nx=m.tx+dd[0], ny=m.ty+dd[1];
          if (walkable(nx,ny)) { target={x:nx,y:ny}; break; }
        }
        if (!target) target = {x:m.tx, y:m.ty};
      }
      if (target) {
        const path = bfs({x:m.tx,y:m.ty}, target);
        if (path && path.length>1) m.nextTile = path[1];
      }
      m.actTimer = (m.type==='slime' ? 0.45 : 0.35);
    }
    if (m.nextTile) {
      const cx=(m.nextTile.x+0.5)*TILE, cy=(m.nextTile.y+0.5)*TILE;
      const dx=cx-m.x, dy=cy-m.y, dd=Math.hypot(dx,dy);
      if (dd < 1.5) { m.x=cx; m.y=cy; m.tx=m.nextTile.x; m.ty=m.nextTile.y; m.nextTile=null; }
      else { m.x += dx/dd*m.speed*dt; m.y += dy/dd*m.speed*dt; }
    }
    if (m.flash>0) m.flash -= dt;
  }

  // monster contact damage
  for (const m of monsters) {
    const d = Math.hypot(m.x-player.x, m.y-player.y);
    if (d < 26 && player.invuln<=0) {
      health = Math.max(0, health-1);
      player.invuln=1.0;
      shake=0.2;
      makeParticle(player.x,player.y,'#ef4444');
      beep(120,0.2,'sawtooth',0.08);
      updateHud();
      // push monster back
      const ang = Math.atan2(m.y-player.y, m.x-player.x);
      m.x += Math.cos(ang)*16; m.y += Math.sin(ang)*16;
    }
  }
  if (health<=0) gameOverState();

  // particles
  for (let i=particles.length-1;i>=0;i--){
    const p=particles[i];
    p.x+=p.vx*dt; p.y+=p.vy*dt; p.vx*=0.9; p.vy*=0.9; p.life-=dt;
    if (p.life<=0) particles.splice(i,1);
  }
  if (shake>0) shake -= dt;
  if (messageTimer>0) messageTimer -= dt;
}

// ===== RENDER =====
function render() {
  ctx.save();
  if (shake>0) ctx.translate((Math.random()-0.5)*shake*10,(Math.random()-0.5)*shake*10);

  // background
  ctx.fillStyle = '#0f172a';
  ctx.fillRect(0,0,W,H);

  if (!grid || !grid.length) { ctx.restore(); return; }

  // floor subtle
  for (let y=0;y<ROWS;y++) for (let x=0;x<COLS;x++){
    const v=grid[y][x];
    const px=x*TILE, py=y*TILE;
    if (v===1) {
      ctx.fillStyle = '#334155';
      ctx.fillRect(px,py,TILE,TILE);
      ctx.strokeStyle='rgba(0,0,0,.35)'; ctx.lineWidth=1; ctx.strokeRect(px,py,TILE,TILE);
    } else {
      ctx.fillStyle = (x+y)%2===0 ? '#1f2937' : '#1a2332';
      ctx.fillRect(px,py,TILE,TILE);
      if (v===2) {
        // exit ladder
        ctx.fillStyle='rgba(16,185,129,.25)'; ctx.fillRect(px,py,TILE,TILE);
        ctx.fillStyle='#10b981';
        for (let i=0;i<4;i++){ ctx.fillRect(px+6+i*9, py+8, 4, TILE-16); }
        ctx.fillStyle='#fbbf24'; ctx.fillRect(px+4, py+6, TILE-8, 4); ctx.fillRect(px+4, py+TILE-10, TILE-8, 4);
      } else if (v===3) {
        ctx.fillStyle='#fbbf24';
        ctx.beginPath(); ctx.arc(px+TILE/2,py+TILE/2,7,0,Math.PI*2); ctx.fill();
        ctx.fillStyle='rgba(251,191,36,.3)'; ctx.beginPath(); ctx.arc(px+TILE/2,py+TILE/2,12,0,Math.PI*2); ctx.fill();
      }
    }
  }

  // particles
  particles.forEach(p => {
    ctx.globalAlpha = Math.max(0, p.life/p.max);
    ctx.fillStyle = p.color;
    ctx.beginPath(); ctx.arc(p.x,p.y,p.r,0,Math.PI*2); ctx.fill();
  });
  ctx.globalAlpha = 1;

  // monsters
  monsters.forEach(m => {
    ctx.save();
    ctx.translate(m.x,m.y);
    const col = m.flash>0 ? '#fbbf24' : (m.type==='slime' ? '#22c55e' : '#a855f7');
    ctx.fillStyle = col;
    ctx.beginPath(); ctx.arc(0,0,12,0,Math.PI*2); ctx.fill();
    ctx.strokeStyle='rgba(0,0,0,.4)'; ctx.lineWidth=2; ctx.stroke();
    // eyes
    ctx.fillStyle='#fff';
    ctx.beginPath(); ctx.arc(-4,-3,2.5,0,Math.PI*2); ctx.fill();
    ctx.beginPath(); ctx.arc(4,-3,2.5,0,Math.PI*2); ctx.fill();
    ctx.fillStyle='#111';
    ctx.beginPath(); ctx.arc(-4+ (player.x-m.x)*0.02, -3,1.2,0,Math.PI*2); ctx.fill();
    ctx.beginPath(); ctx.arc(4+ (player.x-m.x)*0.02, -3,1.2,0,Math.PI*2); ctx.fill();
    ctx.restore();
  });

  if (!player) { ctx.restore(); return; }

  // player
  ctx.fillStyle = player.invuln>0 ? 'rgba(59,130,246,.6)' : '#3b82f6';
  ctx.beginPath(); ctx.arc(0,0,player.r,0,Math.PI*2); ctx.fill();
  ctx.strokeStyle='#bfdbfe'; ctx.lineWidth=2; ctx.stroke();
  // facing indicator
  ctx.strokeStyle='rgba(255,255,255,.7)'; ctx.lineWidth=2;
  ctx.beginPath(); ctx.moveTo(0,0); ctx.lineTo(lastDir.x*14, lastDir.y*14); ctx.stroke();
  ctx.restore();

  // message
  if (messageTimer>0) {
    ctx.fillStyle='rgba(0,0,0,.45)'; ctx.fillRect(W/2-180,H-60,360,40);
    ctx.fillStyle='#fff'; ctx.font='bold 16px Inter, system-ui'; ctx.textAlign='center';
    ctx.fillText(message, W/2, H-35);
    ctx.textAlign='start';
  }
  // pause
  if (paused) {
    ctx.fillStyle='rgba(0,0,0,.6)'; ctx.fillRect(0,0,W,H);
    ctx.fillStyle='#fff'; ctx.font='bold 28px Inter'; ctx.textAlign='center';
    ctx.fillText('Pausa (P)', W/2, H/2);
    ctx.textAlign='start';
  }

  ctx.restore();
}

function loop(ts) {
  const dt = Math.min((ts-lastTime)/1000, 0.05);
  lastTime = ts;
  update(dt);
  render();
  requestAnimationFrame(loop);
}

// ===== INPUT =====
window.addEventListener('keydown', e => {
  keys[e.code] = true;
  if (e.code === 'Space') { e.preventDefault(); }
  if (e.code === 'KeyP') paused = !paused;
  if (e.code === 'KeyR' && gameState==='gameover') resetGame();
});
window.addEventListener('keyup', e => { keys[e.code] = false; });
window.addEventListener('mousemove', e => {
  const rect = canvas.getBoundingClientRect();
  mouse.x = (e.clientX-rect.left)*(W/rect.width);
  mouse.y = (e.clientY-rect.top)*(H/rect.height);
});
startBtn.addEventListener('click', ()=>{ ensureAudio(); if (gameState==='menu') resetGame(); });
retryBtn.addEventListener('click', ()=>{ ensureAudio(); resetGame(); });
soundBtn.addEventListener('click', ()=>{ soundOn=!soundOn; soundBtn.textContent=soundOn?'🔊':'🔇'; });

// prevent scrolling
window.addEventListener('keydown', e => { if (['ArrowUp','ArrowDown','ArrowLeft','ArrowRight','Space'].includes(e.code)) e.preventDefault(); });

requestAnimationFrame(loop);
