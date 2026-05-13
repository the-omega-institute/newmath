(function () {
  "use strict";

  const DATA_URL = "data/bedc_operations.json";
  const state = {
    operations: [],
    operationById: {},
    activeIndex: 0,
    rows: [],
    currentStep: 0,
    playing: false,
    lastFrameMs: 0
  };

  const MODULE_ORDER = [
    "Mark",
    "Hist",
    "Ext",
    "Sig",
    "Cont",
    "Bundle",
    "Unary",
    "Ask",
    "ExternalBinary",
    "Gap",
    "Package",
    "NameCert",
    "Settled",
    "GroundCompiler",
    "CircleUp",
    "FoldUp",
    "MetaCIC",
    "TopologyUp"
  ];

  function byId(id) {
    return document.getElementById(id);
  }

  function clamp(value, min, max) {
    return Math.max(min, Math.min(max, value));
  }

  function activeOperation() {
    return state.operations[state.activeIndex] || null;
  }

  function colorWithAlpha(hex, alpha) {
    const value = hex.replace("#", "");
    if (value.length !== 6) return `rgba(242, 193, 78, ${alpha})`;
    const r = parseInt(value.slice(0, 2), 16);
    const g = parseInt(value.slice(2, 4), 16);
    const b = parseInt(value.slice(4, 6), 16);
    return `rgba(${r}, ${g}, ${b}, ${alpha})`;
  }

  function setupCanvasSize(canvas, width, height) {
    const ratio = window.devicePixelRatio || 1;
    canvas.width = Math.max(1, Math.floor(width * ratio));
    canvas.height = Math.max(1, Math.floor(height * ratio));
    canvas.style.width = `${width}px`;
    canvas.style.height = `${height}px`;
    return ratio;
  }

  function displayValue(value) {
    if (value === undefined || value === null) return "";
    if (value === "") return "<empty>";
    return String(value);
  }

  function drawRows(ctx, rows, visibleRows, cellSize) {
    ctx.fillStyle = "#faf9f5";
    ctx.fillRect(0, 0, rows[0].length * cellSize, visibleRows * cellSize);
    ctx.fillStyle = "#111111";
    for (let y = 0; y < visibleRows; y++) {
      const row = rows[y];
      for (let x = 0; x < row.length; x++) {
        if (row[x] === 1) {
          ctx.fillRect(x * cellSize, y * cellSize, cellSize, cellSize);
        }
      }
    }
  }

  function drawLayers(ctx, operation, visibleRows, cellSize) {
    const maxY = visibleRows * cellSize;
    ctx.save();
    for (const layer of operation.semantic_layers || []) {
      const yStart = Number.isFinite(layer.y_start) ? layer.y_start : 0;
      if (yStart >= visibleRows) continue;
      if (layer.x_end <= layer.x_start) continue;
      const x = layer.x_start * cellSize;
      const w = Math.max(cellSize, (layer.x_end - layer.x_start) * cellSize);
      const y = yStart * cellSize;
      const h = Math.max(cellSize, maxY - y);
      ctx.fillStyle = colorWithAlpha(layer.color || "#f2c14e", 0.18);
      ctx.fillRect(x, y, w, h);
      ctx.strokeStyle = colorWithAlpha(layer.color || "#f2c14e", 0.72);
      ctx.lineWidth = Math.max(1, cellSize * 0.1);
      ctx.strokeRect(x, y, w, h);
    }
    ctx.restore();
  }

  function renderLegend(operation) {
    const legend = byId("bedc-layer-legend");
    if (!legend) return;
    legend.innerHTML = "";
    for (const layer of operation.semantic_layers || []) {
      const item = document.createElement("span");
      const swatch = document.createElement("span");
      const label = document.createElement("span");
      item.className = "bedc-legend-item";
      swatch.className = "bedc-legend-swatch";
      swatch.style.background = layer.color || "#f2c14e";
      label.textContent = `${layer.label} [${layer.x_start}, ${layer.x_end})`;
      item.append(swatch, label);
      legend.appendChild(item);
    }
  }

  function renderMeta(operation) {
    const meta = byId("bedc-operation-meta");
    if (!meta) return;
    const decode = operation.expected_decode || {};
    meta.innerHTML = "";

    const entries = [
      ["manifest", operation.source_manifest || operation.manifest_file],
      ["case", operation.case_name],
      ["steps", operation.evolution_steps],
      ["verdict", decode.verdict || "pass"],
      ["payload", `[${decode.payload_start}, ${decode.payload_start + decode.payload_len})`]
    ];

    for (const [label, value] of entries) {
      const row = document.createElement("div");
      const key = document.createElement("span");
      const val = document.createElement("code");
      row.className = "bedc-meta-card";
      key.textContent = label;
      val.textContent = displayValue(value);
      row.append(key, val);
      meta.appendChild(row);
    }
  }

  function render() {
    const operation = activeOperation();
    const canvas = byId("bedc-spacetime-canvas");
    const stepLabel = byId("bedc-step-label");
    if (!operation || !canvas || state.rows.length === 0) return;

    const visibleRows = clamp(state.currentStep + 1, 1, state.rows.length);
    const host = canvas.parentElement;
    const hostWidth = host ? Math.max(1, host.clientWidth - 2) : 900;
    const hostHeight = host ? Math.max(1, host.clientHeight - 2) : 420;
    const width = state.rows[0].length;
    const fitCellSize = Math.floor(Math.min(hostWidth / width, hostHeight / visibleRows));
    const cellSize = Math.max(1, Math.min(8, fitCellSize));
    const cssWidth = width * cellSize;
    const cssHeight = visibleRows * cellSize;
    const ratio = setupCanvasSize(canvas, cssWidth, cssHeight);
    const ctx = canvas.getContext("2d");

    ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
    drawRows(ctx, state.rows, visibleRows, cellSize);
    drawLayers(ctx, operation, visibleRows, cellSize);

    if (stepLabel) {
      stepLabel.textContent = `${state.currentStep} / ${state.rows.length - 1}`;
    }
  }

  function setOperation(index) {
    const operation = state.operations[index];
    if (!operation) return;
    state.activeIndex = index;
    state.rows = window.Rule110Evolve.evolve(
      operation.initial_row,
      operation.evolution_steps
    );
    state.currentStep = Math.min(96, state.rows.length - 1);

    const scrubber = byId("bedc-step-scrubber");
    if (scrubber) {
      scrubber.min = "0";
      scrubber.max = String(state.rows.length - 1);
      scrubber.step = "1";
      scrubber.value = String(state.currentStep);
    }
    renderLegend(operation);
    renderMeta(operation);
    render();
  }

  function groupOperationsByModule() {
    const groups = {};
    for (const operation of state.operations) {
      const moduleName = operation.module || "Other";
      if (!groups[moduleName]) groups[moduleName] = [];
      groups[moduleName].push(operation);
    }
    return groups;
  }

  function appendOptionsForModule(select, moduleName, operations) {
    const group = document.createElement("optgroup");
    group.label = moduleName;
    for (const operation of operations) {
      const option = document.createElement("option");
      option.value = operation.id;
      option.textContent = `${operation.manifest_file || operation.name} · ${operation.case_name}`;
      group.appendChild(option);
    }
    select.appendChild(group);
  }

  function populateOperationSelect(select) {
    const groups = groupOperationsByModule();
    const seen = new Set();

    select.innerHTML = "";
    for (const moduleName of MODULE_ORDER) {
      if (!groups[moduleName]) continue;
      appendOptionsForModule(select, moduleName, groups[moduleName]);
      seen.add(moduleName);
    }
    for (const moduleName of Object.keys(groups).sort()) {
      if (seen.has(moduleName)) continue;
      appendOptionsForModule(select, moduleName, groups[moduleName]);
    }
  }

  function setPlaying(next) {
    state.playing = next;
    const button = byId("bedc-play-toggle");
    if (button) button.textContent = next ? "Pause" : "Play";
  }

  function tick(now) {
    if (state.playing) {
      const speed = byId("bedc-speed-slider");
      const fps = speed ? Number(speed.value) : 12;
      const interval = 1000 / clamp(fps, 1, 60);
      if (now - state.lastFrameMs >= interval) {
        state.lastFrameMs = now;
        state.currentStep += 1;
        if (state.currentStep >= state.rows.length) {
          state.currentStep = 0;
        }
        const scrubber = byId("bedc-step-scrubber");
        if (scrubber) scrubber.value = String(state.currentStep);
        render();
      }
    }
    window.requestAnimationFrame(tick);
  }

  function bindControls() {
    const select = byId("bedc-operation-select");
    const scrubber = byId("bedc-step-scrubber");
    const play = byId("bedc-play-toggle");
    const speed = byId("bedc-speed-slider");
    const speedLabel = byId("bedc-speed-label");

    if (select) {
      populateOperationSelect(select);
      select.addEventListener("change", () => {
        const index = state.operationById[select.value];
        setPlaying(false);
        setOperation(Number.isFinite(index) ? index : 0);
      });
    }

    if (scrubber) {
      scrubber.addEventListener("input", () => {
        state.currentStep = Number(scrubber.value);
        render();
      });
    }

    if (play) {
      play.addEventListener("click", () => setPlaying(!state.playing));
    }

    if (speed && speedLabel) {
      const updateSpeed = () => {
        speedLabel.textContent = `${speed.value} fps`;
      };
      speed.addEventListener("input", updateSpeed);
      updateSpeed();
    }

    window.addEventListener("resize", render);
  }

  async function init() {
    const host = byId("bedc-spacetime-app");
    if (!host || !window.Rule110Evolve) return;
    try {
      const response = await fetch(DATA_URL);
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      const data = await response.json();
      state.operations = data.operations || [];
      state.operationById = {};
      state.operations.forEach((operation, index) => {
        state.operationById[operation.id] = index;
      });
      bindControls();
      setOperation(0);
      window.requestAnimationFrame(tick);
    } catch (err) {
      host.textContent = `Failed to load BEDC Rule 110 data: ${err.message}`;
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
