(() => {
  "use strict";
  const api = window.AgdaOperadApp;
  const canvas = document.querySelector("canvas");
  const ctx = canvas.getContext("2d");
  const utf8 = new TextDecoder();
  const natural = n => BigInt(Math.max(0, Math.round(n)));
  let app, lastWire, pointer, lastTime;

  function draw() {
    const wire = api.renderWorkbenchWire(app);
    if (wire === lastWire) return;
    lastWire = wire;
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    for (const line of wire.split("\n")) {
      if (!line) continue;
      const [op, ...args] = line.split(" ");
      const [a, b, c, x, y, w, h] = args.map(Number);
      const colour = `rgb(${a}, ${b}, ${c})`;
      switch (op) {
        case "SAVE": ctx.save(); break;
        case "RESTORE": ctx.restore(); break;
        case "TRANSFORM": ctx.transform(a/b, 0, 0, a/b, c/b, x/b); break;
        case "CLIP":
          ctx.beginPath(); ctx.rect(a, b, c, x); ctx.clip(); break;
        case "FILL":
          ctx.fillStyle = colour; ctx.fillRect(x, y, w, h); break;
        case "STROKE":
          ctx.strokeStyle = colour;
          if (w && h) ctx.strokeRect(x + 0.5, y + 0.5, w - 1, h - 1);
          break;
        case "TEXT": {
          const pairs = args[7].match(/[0-9a-f]{2}/gi) || [];
          const text = utf8.decode(Uint8Array.from(pairs, p => parseInt(p, 16)));
          ctx.save(); ctx.beginPath(); ctx.rect(x, y, w, h); ctx.clip();
          ctx.font = "13px 'IBM Plex Mono', monospace"; ctx.textBaseline = "middle";
          ctx.fillStyle = colour; ctx.fillText(text, x + 6, y + h/2);
          ctx.restore(); break;
        }
        case "LINE":
          ctx.strokeStyle = colour; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(w, h); ctx.stroke(); break;
        default: throw new Error("Unknown Agda draw command " + op);
      }
    }
  }

  function resize() {
    const bounds = canvas.getBoundingClientRect();
    const w = Math.max(1, Math.round(bounds.width)), h = Math.max(1, Math.round(bounds.height));
    canvas.width = w; canvas.height = h; lastWire = undefined;
    app = app === undefined ? api.initWorkbench(BigInt(w))(BigInt(h))
                            : api.resizeWorkbench(BigInt(w))(BigInt(h))(app);
    draw();
  }
  function pan(direction, step) {
    app = api.panWorkbench(BigInt(direction))(natural(step))(app);
  }
  function position(e) {
    const r = canvas.getBoundingClientRect();
    return [Math.floor((e.clientX-r.left)*canvas.width/r.width),
            Math.floor((e.clientY-r.top)*canvas.height/r.height)];
  }
  canvas.addEventListener("pointerdown", e => {
    if (!e.isPrimary || e.button !== 0) return;
    canvas.focus(); canvas.setPointerCapture(e.pointerId);
    const [x, y] = position(e);
    pointer = { id: e.pointerId, x, y, dragged: false };
  });
  canvas.addEventListener("pointermove", e => {
    if (pointer?.id !== e.pointerId) return;
    const [x, y] = position(e), dx = x - pointer.x, dy = y - pointer.y;
    if (!pointer.dragged && Math.abs(dx) + Math.abs(dy) < 3) return;
    pointer = { id: e.pointerId, x, y, dragged: true };
    if (dx) pan(dx < 0 ? 0 : 1, Math.abs(dx));
    if (dy) pan(dy < 0 ? 2 : 3, Math.abs(dy));
    draw();
  });
  canvas.addEventListener("pointerup", e => {
    if (pointer?.id !== e.pointerId) return;
    const [x, y] = position(e);
    if (!pointer.dragged && x >= 0 && y >= 0 && x < canvas.width && y < canvas.height)
      app = api.clickWorkbench(natural(x))(natural(y))(app);
    pointer = undefined; draw();
  });
  canvas.addEventListener("lostpointercapture", () => { pointer = undefined; });
  canvas.addEventListener("wheel", e => {
    e.preventDefault();
    if (e.deltaY) { pan(e.deltaY < 0 ? 4 : 5, 1); draw(); }
  }, { passive: false });
  const keys = new Map([["ArrowLeft",0],["ArrowRight",1],["ArrowUp",2],["ArrowDown",3],["Escape",6]]);
  canvas.addEventListener("keydown", e => {
    if (!keys.has(e.key)) return;
    e.preventDefault(); pan(keys.get(e.key), 12); draw();
  });
  function tick(time) {
    const now = Math.floor(time);
    if (lastTime !== undefined) {
      app = api.tickWorkbench(natural(now - lastTime))(app);
      draw();
    }
    lastTime = now;
    requestAnimationFrame(tick);
  }
  window.addEventListener("resize", resize);
  resize(); requestAnimationFrame(tick);
})();
