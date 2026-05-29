#!/usr/bin/env python3
"""Wrap dag.svg (dark) into a zoomable/pannable dark-mode dag.html.
Run after regenerating dag.svg from dag.dot. No external JS deps."""
import os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
svg = open(os.path.join(ROOT, 'dag.svg')).read()
svg_inner = svg[svg.find('<svg'):]  # drop XML decl/doctype

HTML = '''<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>PSS 証明依存 DAG</title>
<style>
  html,body{margin:0;height:100%;background:#1e1e1e;color:#eaeaea;
    font-family:system-ui,sans-serif;overflow:hidden;}
  #bar{position:fixed;top:0;left:0;right:0;height:42px;display:flex;
    align-items:center;gap:8px;padding:0 12px;background:#262626;
    border-bottom:1px solid #444;z-index:10;font-size:13px;}
  #bar b{color:#fff;} #bar .leg{margin-left:auto;display:flex;gap:14px;}
  .chip{display:inline-flex;align-items:center;gap:5px;}
  .sw{width:12px;height:12px;border-radius:2px;display:inline-block;border:1px solid #666;}
  button{background:#333;color:#eaeaea;border:1px solid #555;border-radius:4px;
    padding:3px 9px;cursor:pointer;font-size:13px;} button:hover{background:#444;}
  #stage{position:fixed;top:42px;left:0;right:0;bottom:0;overflow:hidden;cursor:grab;
    touch-action:none;-ms-touch-action:none;}
  #stage.drag{cursor:grabbing;}
  #vp{transform-origin:0 0;} #vp svg{display:block;}
  #hint{position:fixed;bottom:8px;right:12px;font-size:11px;color:#888;z-index:10;}
</style></head>
<body>
<div id="bar">
  <b>PSS 証明依存 DAG</b>
  <button onclick="zoom(1.25)">＋</button>
  <button onclick="zoom(0.8)">－</button>
  <button onclick="fit()">Fit</button>
  <button onclick="reset()">100%</button>
  <span class="leg">
    <span class="chip"><span class="sw" style="background:#2e5d34"></span>証明済</span>
    <span class="chip"><span class="sw" style="background:#6b2b30"></span>未証明</span>
    <span class="chip"><span class="sw" style="background:#7a5320"></span>作業中</span>
    <span class="chip">矢印 X→Y = X を使って Y を証明 / ゴール §8.7 最下段</span>
  </span>
</div>
<div id="stage"><div id="vp">__SVG__</div></div>
<div id="hint">PC: ホイール=拡大 / ドラッグ=移動　スマホ: ピンチ=拡大 / スワイプ=移動</div>
<script>
const stage=document.getElementById('stage'), vp=document.getElementById('vp');
let scale=1, tx=0, ty=0;
function apply(){vp.style.transform=`translate(${tx}px,${ty}px) scale(${scale})`;}
function zoomAt(f,px,py){tx=px-(px-tx)*f; ty=py-(py-ty)*f; scale*=f; apply();}
function zoom(f){const r=stage.getBoundingClientRect();zoomAt(f,r.width/2,r.height/2);}
function reset(){scale=1;tx=0;ty=0;apply();}
function fit(){const svg=vp.querySelector('svg');const r=stage.getBoundingClientRect();
  const w=svg.width.baseVal.value||svg.viewBox.baseVal.width;
  const h=svg.height.baseVal.value||svg.viewBox.baseVal.height;
  const s=Math.min(r.width/w, r.height/h)*0.96; scale=s;
  tx=(r.width-w*s)/2; ty=(r.height-h*s)/2; apply();}
function rel(cx,cy){const r=stage.getBoundingClientRect();return [cx-r.left,cy-r.top];}

/* --- mouse (PC) --- */
stage.addEventListener('wheel',e=>{e.preventDefault();
  const [mx,my]=rel(e.clientX,e.clientY);
  zoomAt(e.deltaY<0?1.12:0.893,mx,my);
},{passive:false});
let dragging=false,sx,sy;
stage.addEventListener('mousedown',e=>{dragging=true;stage.classList.add('drag');sx=e.clientX-tx;sy=e.clientY-ty;});
window.addEventListener('mousemove',e=>{if(dragging){tx=e.clientX-sx;ty=e.clientY-sy;apply();}});
window.addEventListener('mouseup',()=>{dragging=false;stage.classList.remove('drag');});

/* --- touch (mobile): 1-finger pan, 2-finger pinch-zoom --- */
let tPan=null, tPinch=null;   // pan: {x,y}; pinch: {d, mx, my}
function dist(a,b){return Math.hypot(a.clientX-b.clientX, a.clientY-b.clientY);}
stage.addEventListener('touchstart',e=>{e.preventDefault();
  if(e.touches.length===1){
    tPinch=null; tPan={x:e.touches[0].clientX-tx, y:e.touches[0].clientY-ty};
  }else if(e.touches.length>=2){
    tPan=null; const [mx,my]=rel((e.touches[0].clientX+e.touches[1].clientX)/2,
                                 (e.touches[0].clientY+e.touches[1].clientY)/2);
    tPinch={d:dist(e.touches[0],e.touches[1]), mx, my};
  }
},{passive:false});
stage.addEventListener('touchmove',e=>{e.preventDefault();
  if(e.touches.length===1 && tPan){
    tx=e.touches[0].clientX-tPan.x; ty=e.touches[0].clientY-tPan.y; apply();
  }else if(e.touches.length>=2 && tPinch){
    const nd=dist(e.touches[0],e.touches[1]);
    const [mx,my]=rel((e.touches[0].clientX+e.touches[1].clientX)/2,
                      (e.touches[0].clientY+e.touches[1].clientY)/2);
    if(tPinch.d>0){ zoomAt(nd/tPinch.d, mx, my); }
    tPinch={d:nd, mx, my};
  }
},{passive:false});
stage.addEventListener('touchend',e=>{
  if(e.touches.length===0){tPan=null;tPinch=null;}
  else if(e.touches.length===1){tPinch=null;tPan={x:e.touches[0].clientX-tx,y:e.touches[0].clientY-ty};}
});

window.addEventListener('load',fit);
window.addEventListener('resize',fit);
</script></body></html>'''
open(os.path.join(ROOT,'dag.html'),'w').write(HTML.replace('__SVG__', svg_inner))
print("dag.html regenerated from dag.svg")
