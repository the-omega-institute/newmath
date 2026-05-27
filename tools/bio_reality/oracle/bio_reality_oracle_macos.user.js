// ==UserScript==
// @name         BioReality Oracle Bridge (macOS, multi-turn)
// @namespace    omega-bio-reality
// @version      2.1
// @description  BioReality-pipeline ChatGPT bridge bio-2.0 with automath-stable waiting and BEDC project/PDF routing. Talks to bio_reality_oracle_server.py on :8769.
// @match        https://chatgpt.com/*
// @match        https://chat.openai.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @connect      localhost
// @connect      127.0.0.1
// @run-at       document-start
// @noframes
// ==/UserScript==

(function () {
  "use strict";

  try { console.log("[bio] userscript IIFE entered, version bio-2.0"); } catch {}

  try {
    if (window.top !== window.self) {
      try { console.log("[bio] exit: in iframe (top!=self)"); } catch {}
      return;
    }
  } catch {
    try { console.log("[bio] exit: window.top access threw"); } catch {}
    return;
  }
  if (window.location.pathname.startsWith("/backend-api/")) {
    try { console.log("[bio] exit: backend-api path"); } catch {}
    return;
  }
  if (window.location.href.includes("/sentinel/")) {
    try { console.log("[bio] exit: sentinel path"); } catch {}
    return;
  }
  try { console.log("[bio] passed early-return gates, pathname=", window.location.pathname); } catch {}

  const SERVER = "http://127.0.0.1:8769";
  const POLL_INTERVAL = 30000;
  const STABLE_CHECKS = 3;
  const STABLE_INTERVAL = 60000;
  const MAX_WAIT = 7200000;
  const DEFAULT_MIN_RESPONSE_LENGTH = 1000;
  const REQUIRE_FOREGROUND_TO_CLAIM = false;
  const SCRIPT_VERSION = "bio-2.1";
  const BIOREALITY_PROJECT_PREFIX = "/g/g-p-6a098a6e69688191a6afd91978c585ef-ge-ben-ha-gen-zhi-lu";
  const BIOREALITY_PROJECT_HOME = `https://chatgpt.com${BIOREALITY_PROJECT_PREFIX}/project`;

  function isInsideBioRealityProject() {
    return window.location.pathname.startsWith(BIOREALITY_PROJECT_PREFIX);
  }

  function bioFlagFromUrl() {
    const m = window.location.search.match(/[?&]bio=([^&]+)/);
    return m ? m[1] : "";
  }

  function projectEntryUrl(flag = bioFlagFromUrl()) {
    return `${BIOREALITY_PROJECT_HOME}${flag ? `?bio=${encodeURIComponent(flag)}` : ""}`;
  }

  function detectAgentId() {
    const urlParam = new URLSearchParams(window.location.search).get("bio");
    if (urlParam) {
      const id = `bio_${urlParam}`;
      try { sessionStorage.setItem("bio_agent_id", id); } catch {}
      return id;
    }
    try {
      const navEntries = performance.getEntriesByType("navigation");
      if (navEntries.length > 0) {
        const origUrl = new URL(navEntries[0].name);
        const origParam = origUrl.searchParams.get("bio");
        if (origParam) {
          const id = `bio_${origParam}`;
          try { sessionStorage.setItem("bio_agent_id", id); } catch {}
          return id;
        }
      }
    } catch {}
    try {
      return sessionStorage.getItem("bio_agent_id") || "";
    } catch { return ""; }
  }

  const AGENT_ID = detectAgentId();
  if (!AGENT_ID) return;

  let busy = false;
  let active = (() => {
    const urlOptIn = window.location.search.includes("bio=");
    try {
      if (urlOptIn) sessionStorage.setItem("bio_active", "1");
      const storedActive = sessionStorage.getItem("bio_active") === "1";
      return storedActive && (urlOptIn || isInsideBioRealityProject());
    } catch {
      return urlOptIn;
    }
  })();

  // ── Logging ──────────────────────────────────────────────────────────
  const logHistory = [];
  function log(msg) {
    const ts = new Date().toLocaleTimeString();
    const entry = `${ts} ${msg}`;
    console.log(`[bio] ${entry}`);
    logHistory.push(entry);
    if (logHistory.length > 20) logHistory.shift();
    updatePanel();
  }

  function toggleActive() {
    active = !active;
    try { sessionStorage.setItem("bio_active", active ? "1" : "0"); } catch {}
    log(active ? "ACTIVATED — polling will start (this tab only)" : "PAUSED — your ChatGPT is free");
    updatePanel();
  }

  // ── Status panel ─────────────────────────────────────────────────────
  let panel = null;
  function ensurePanel() {
    if (panel && document.body.contains(panel)) return;
    panel = document.createElement("div");
    panel.id = "bio-oracle-panel";
    panel.style.cssText = `
      position: fixed; bottom: 12px; right: 12px; z-index: 99999;
      background: #10251f; color: #90f0d0; font-family: monospace; font-size: 11px;
      padding: 8px 12px; border-radius: 6px; max-width: 460px; max-height: 320px;
      overflow-y: auto; box-shadow: 0 2px 12px rgba(20,120,90,0.5); opacity: 0.93;
      line-height: 1.4; border: 1px solid #28b89a;
    `;
    document.body.appendChild(panel);
  }

  function updatePanel() {
    ensurePanel();
    const statusColor = active ? (busy ? "#ffd166" : "#90f0d0") : "#ff6b6b";
    const statusText = active ? (busy ? "BUSY" : "ACTIVE") : "PAUSED";
    const btnText = active ? "⏸ Pause" : "▶ Start";
    const btnColor = active ? "#ff6b6b" : "#2dd4bf";
    const lines = logHistory.slice(-10).map(l => `<div>${l}</div>`).join("");
    panel.innerHTML = `
      <div style="display:flex;justify-content:space-between;align-items:center;gap:8px">
        <b style="color:#d7fff2">[bio] BioReality Oracle ${SCRIPT_VERSION}</b>
        <span style="color:${statusColor};font-weight:bold">${statusText}</span>
        <button id="bio-toggle" style="background:${btnColor};color:#000;border:none;border-radius:3px;padding:2px 8px;cursor:pointer;font-size:11px;font-weight:bold">${btnText}</button>
      </div>
      <hr style="border-color:#1e8f78;margin:4px 0">
      ${lines}`;
    const btn = document.getElementById("bio-toggle");
    if (btn) btn.addEventListener("click", toggleActive);
  }

  // ── HTTP helpers ─────────────────────────────────────────────────────
  function serverGet(path) {
    return new Promise((resolve, reject) => {
      const sep = path.includes("?") ? "&" : "?";
      const meta = `${sep}script_version=${encodeURIComponent(SCRIPT_VERSION)}`
        + `&page_url=${encodeURIComponent(window.location.href)}`
        + `&chatgpt_url=${encodeURIComponent(currentChatUrl())}`;
      GM_xmlhttpRequest({
        method: "GET",
        url: `${SERVER}${path}${meta}`,
        timeout: 10000,
        onload: (r) => {
          try { resolve(JSON.parse(r.responseText)); }
          catch (e) { reject(e); }
        },
        onerror: () => reject(new Error("network error")),
        ontimeout: () => reject(new Error("timeout")),
      });
    });
  }

  function serverPost(path, data) {
    return new Promise((resolve, reject) => {
      const payload = Object.assign({}, data || {}, {
        script_version: SCRIPT_VERSION,
        page_url: window.location.href,
        chatgpt_url: (data && data.chatgpt_url) || currentChatUrl(),
      });
      GM_xmlhttpRequest({
        method: "POST",
        url: `${SERVER}${path}`,
        headers: { "Content-Type": "application/json" },
        data: JSON.stringify(payload),
        timeout: 30000,
        onload: (r) => {
          try { resolve(JSON.parse(r.responseText)); }
          catch (e) { reject(e); }
        },
        onerror: () => reject(new Error("network error")),
        ontimeout: () => reject(new Error("timeout")),
      });
    });
  }

  function sleep(ms) {
    return new Promise((r) => setTimeout(r, ms));
  }

  function foregroundState() {
    return `visibility=${document.visibilityState}, focus=${document.hasFocus()}`;
  }

  function isForegroundReady() {
    if (!REQUIRE_FOREGROUND_TO_CLAIM) return true;
    return document.visibilityState === "visible" && document.hasFocus();
  }

  // ── Persistent task state (survives page navigation) ─────────────────
  function saveTaskState(task) {
    tabSet("current_task", JSON.stringify(task));
    tabSet("task_phase", "pending");
  }
  function loadTaskState() {
    try {
      const s = tabGet("current_task", "");
      return s ? JSON.parse(s) : null;
    } catch { return null; }
  }
  function getTaskPhase() {
    return tabGet("task_phase", "");
  }
  function setTaskPhase(phase) {
    tabSet("task_phase", phase);
  }
  function clearTaskState() {
    tabSet("current_task", "");
    tabSet("task_phase", "");
  }
  function getInFlightTaskId() {
    return tabGet("in_flight_task_id", "");
  }
  function setInFlightTaskId(id) {
    tabSet("in_flight_task_id", id || "");
    // Also stamp the URL we were on when we became busy with this task.
    if (id) {
      tabSet("in_flight_url", window.location.href);
      tabSet("in_flight_started_at", Date.now());
    } else {
      tabSet("in_flight_url", "");
      tabSet("in_flight_started_at", 0);
    }
  }
  function getInFlightUrl() {
    return tabGet("in_flight_url", "");
  }
  function getInFlightAgeMs() {
    const ts = tabGet("in_flight_started_at", 0);
    return ts ? (Date.now() - ts) : 0;
  }

  // ── DOM helpers ──────────────────────────────────────────────────────

  function findPromptInput() {
    for (const sel of [
      "#prompt-textarea",
      "div.ProseMirror[contenteditable='true']",
      "[id='prompt-textarea']",
      "div[contenteditable='true'][role='textbox']",
      "div[contenteditable='true']",
    ]) {
      const el = document.querySelector(sel);
      if (el) return el;
    }
    return null;
  }

  function findFileInput() {
    // ChatGPT has a hidden file input on the composer
    return document.querySelector("input[type='file']");
  }

  // ── PDF upload (ported from automath chatgpt_oracle_macos.user.js) ────
  async function waitForUploadComplete(timeoutMs = 60000) {
    log("Waiting for PDF upload to complete...");
    const start = Date.now();
    while (Date.now() - start < timeoutMs) {
      await sleep(2000);
      const uploading =
        document.querySelector("[class*='uploading']") ||
        document.querySelector("[class*='progress']") ||
        document.querySelector("[role='progressbar']") ||
        document.querySelector("[class*='loading']");
      const attached =
        document.querySelector("[class*='attachment']") ||
        document.querySelector("[class*='file-chip']") ||
        document.querySelector("[data-testid*='attachment']") ||
        document.querySelector("[class*='uploaded']") ||
        document.querySelector("img[alt*='pdf']") ||
        document.querySelector("[class*='file']");
      const elapsed = Math.floor((Date.now() - start) / 1000);
      if (!uploading && attached) {
        log(`PDF upload complete (${elapsed}s), attachment visible`);
        return true;
      }
      const sendBtn = findSendButton();
      if (sendBtn && !sendBtn.disabled && elapsed > 5) {
        log(`PDF upload likely complete (${elapsed}s), send button enabled`);
        return true;
      }
      if (elapsed % 10 === 0 && elapsed > 0) {
        log(`Upload waiting... ${elapsed}s (uploading=${!!uploading}, attached=${!!attached})`);
      }
    }
    log("Upload wait timeout — proceeding anyway");
    return false;
  }

  async function uploadPDF(base64Data, fileName) {
    log(`PDF upload: ${fileName} (${(base64Data.length * 0.75 / 1024).toFixed(0)} KB)`);
    const byteChars = atob(base64Data);
    const byteArray = new Uint8Array(byteChars.length);
    for (let i = 0; i < byteChars.length; i++) byteArray[i] = byteChars.charCodeAt(i);
    const file = new File([byteArray], fileName, { type: "application/pdf" });

    let injected = false;

    // Method 1: hidden file input
    const fileInput = findFileInput();
    if (fileInput) {
      try {
        const dt = new DataTransfer();
        dt.items.add(file);
        fileInput.files = dt.files;
        fileInput.dispatchEvent(new Event("change", { bubbles: true }));
        log("PDF: injected via file input");
        injected = true;
      } catch (e) {
        log(`PDF file input failed: ${e.message}`);
      }
    }

    // Method 2: click attach button, then file input
    if (!injected) {
      const attachBtn = document.querySelector(
        "button[aria-label='Attach files'], button[aria-label='Upload file'], " +
        "button[data-testid='composer-attach-button'], button[aria-haspopup='menu']"
      );
      if (attachBtn) {
        log("PDF: clicking attach button...");
        attachBtn.click();
        await sleep(1000);
        const fi2 = document.querySelector("input[type='file']");
        if (fi2) {
          try {
            const dt2 = new DataTransfer();
            dt2.items.add(file);
            fi2.files = dt2.files;
            fi2.dispatchEvent(new Event("change", { bubbles: true }));
            log("PDF: injected after clicking attach");
            injected = true;
          } catch (e) {
            log(`PDF inject after attach failed: ${e.message}`);
          }
        }
      }
    }

    // Method 3: drag-drop on composer
    if (!injected) {
      log("PDF: trying drag-drop...");
      const dropTarget =
        document.querySelector("form") ||
        findPromptInput()?.closest("div") ||
        document.querySelector("[class*='composer']");
      if (dropTarget) {
        const dt3 = new DataTransfer();
        dt3.items.add(file);
        for (const evtType of ["dragenter", "dragover", "drop"]) {
          dropTarget.dispatchEvent(new DragEvent(evtType, {
            bubbles: true, cancelable: true, dataTransfer: dt3,
          }));
          await sleep(300);
        }
        log("PDF: drag-drop dispatched");
        injected = true;
      }
    }

    if (!injected) {
      log("PDF: ALL METHODS FAILED — continuing without PDF");
      return false;
    }
    await waitForUploadComplete(60000);
    return true;
  }

  function findSendButton(allowDisabled = false) {
    for (const sel of [
      "button[data-testid='send-button']",
      "button[data-testid='composer-send-button']",
      "button[aria-label='Send prompt']",
      "button[aria-label='发送提示']",
      "button[aria-label='Send']",
      "button[aria-label='Send message']",
      "button[aria-label='Submit']",
    ]) {
      const el = document.querySelector(sel);
      if (el && (allowDisabled || !el.disabled)) return el;
    }
    for (const btn of document.querySelectorAll("button[data-testid]")) {
      const tid = btn.getAttribute("data-testid") || "";
      if (tid.toLowerCase().includes("send") && (allowDisabled || !btn.disabled)) return btn;
    }
    function isNonSendButton(btn) {
      const tid = (btn.getAttribute("data-testid") || "").toLowerCase();
      const label = (btn.getAttribute("aria-label") || "").toLowerCase();
      const text = (btn.textContent || "").toLowerCase();
      const all = tid + " " + label + " " + text;
      return /plus|attach|file|添加|文件|mic|voice|听写|dictation|new|model|专业|search|搜索/.test(all);
    }
    const formAreas = [
      document.querySelector("form"),
      document.querySelector("[class*='composer']"),
      document.querySelector("[class*='input-area']"),
      document.querySelector("[class*='prompt']")?.closest("div[class]"),
    ].filter(Boolean);
    for (const area of formAreas) {
      for (const btn of area.querySelectorAll("button:not([disabled])")) {
        if (isNonSendButton(btn)) continue;
        const svg = btn.querySelector("svg");
        if (svg) {
          const paths = svg.querySelectorAll("path, polyline, line");
          if (paths.length > 0 && paths.length < 5) {
            const rect = btn.getBoundingClientRect();
            if (rect.width > 0 && rect.height > 0) return btn;
          }
        }
      }
    }
    const promptInput = findPromptInput();
    if (promptInput) {
      let container = promptInput.parentElement;
      for (let depth = 0; depth < 6 && container; depth++) {
        const btns = container.querySelectorAll("button:not([disabled])");
        for (const btn of btns) {
          if (isNonSendButton(btn)) continue;
          if (btn.querySelector("svg")) return btn;
        }
        container = container.parentElement;
      }
    }
    return null;
  }

  function isOnNewChatPage() {
    const msgs = document.querySelectorAll("[data-message-author-role]");
    return msgs.length === 0;
  }

  function pinToProject(url) {
    if (!url) return url;
    try {
      const u = new URL(url, window.location.origin);
      // already inside any /g/<slug>/ namespace — trust it
      if (/^\/g\/[^/]+\//.test(u.pathname)) return u.toString();
      if (!BIOREALITY_PROJECT_PREFIX) return u.toString();
      // bare /c/<id> — splice in the BioReality project prefix
      const m = u.pathname.match(/^\/c\/[a-f0-9-]{6,}/);
      if (m) {
        u.pathname = `${BIOREALITY_PROJECT_PREFIX}${m[0]}`;
        return u.toString();
      }
      // bare root or other path — return as-is, caller decides
      return u.toString();
    } catch {
      return url;
    }
  }

  function currentChatUrl() {
    const href = window.location.href;
    if (/\/c\/[a-f0-9-]{6,}/.test(href)) {
      return pinToProject(href.split("?")[0]);
    }
    return "";
  }

  function ensureInProject() {
    const href = window.location.href;
    if (!/\/c\/[a-f0-9-]{6,}/.test(href)) return false;
    if (!BIOREALITY_PROJECT_PREFIX || window.location.pathname.startsWith(BIOREALITY_PROJECT_PREFIX)) return false;
    const pinned = pinToProject(href);
    if (pinned !== href) {
      log(`drift detected — navigating ${href.slice(-40)} → project-pinned`);
      window.location.href = pinned;
      return true;
    }
    return false;
  }

  function findNewChatButton() {
    for (const sel of [
      "button[data-testid='new-chat-button']",
      "a[data-testid='new-chat-button']",
      "button[aria-label='New chat']",
      "button[aria-label='New Chat']",
      "button[aria-label='新聊天']",
      "button[aria-label='新建聊天']",
      "a[href='/']",
      "a[href='/?model=']",
      "[data-testid='create-new-chat-button']",
      "[data-testid='create-new-chat']",
    ]) {
      const el = document.querySelector(sel);
      if (el) return el;
    }
    // Fallback: scan sidebar for an element with text content "New chat" / "新聊天"
    for (const el of document.querySelectorAll("a, button")) {
      const txt = (el.textContent || "").trim();
      if (/^(\+\s*)?(New chat|New Chat|新聊天|新建聊天)$/i.test(txt)) return el;
    }
    return null;
  }

  async function clickNewChatButton() {
    const btn = findNewChatButton();
    if (!btn) return false;
    btn.click();
    await sleep(2000); // SPA transition settle
    // Verify we landed on fresh chat
    return isOnNewChatPage();
  }

  // ── Enter prompt (verbatim) ──────────────────────────────────────────
  async function enterPrompt(text) {
    log(`Entering prompt (${text.length} chars)...`);
    const input = findPromptInput();
    if (!input) { log("ERROR: prompt input not found"); return false; }
    input.focus();
    await sleep(300);
    document.execCommand("selectAll", false, null);
    document.execCommand("delete", false, null);
    await sleep(200);
    let success = false;
    try {
      input.focus();
      const CHUNK = 4000;
      if (text.length <= CHUNK) {
        document.execCommand("insertText", false, text);
      } else {
        for (let i = 0; i < text.length; i += CHUNK) {
          document.execCommand("insertText", false, text.slice(i, i + CHUNK));
          await sleep(50);
        }
      }
      await sleep(500);
      if ((input.textContent || "").length > 10) {
        success = true;
        log("Prompt: inserted via execCommand (ProseMirror-native)");
      }
    } catch (e) { log(`execCommand failed: ${e.message}`); }
    if (!success) {
      try {
        await navigator.clipboard.writeText(text);
        input.focus();
        document.execCommand("paste");
        await sleep(500);
        if ((input.textContent || "").length > 10) {
          success = true;
          log("Prompt: pasted via clipboard API");
        }
      } catch (e) { log(`Clipboard paste failed: ${e.message}`); }
    }
    if (!success) {
      try {
        const clipData = new DataTransfer();
        clipData.setData("text/plain", text);
        input.dispatchEvent(new ClipboardEvent("paste", {
          bubbles: true, cancelable: true, clipboardData: clipData,
        }));
        await sleep(500);
        if ((input.textContent || "").length > 10) {
          success = true;
          log("Prompt: pasted via synthetic ClipboardEvent");
        }
      } catch (e) { log(`Synthetic paste failed: ${e.message}`); }
    }
    if (!success) {
      const escaped = text.replace(/&/g, "&amp;").replace(/</g, "&lt;")
                          .replace(/>/g, "&gt;").replace(/\n/g, "<br>");
      input.innerHTML = `<p>${escaped}</p>`;
      input.dispatchEvent(new InputEvent("input", {
        bubbles: true, cancelable: true, inputType: "insertText", data: text,
      }));
      input.dispatchEvent(new Event("change", { bubbles: true }));
      await sleep(500);
      log("Prompt: set via innerHTML (last resort)");
      success = (input.textContent || "").length > 0;
    }
    if (success) {
      input.focus();
      const sel = window.getSelection();
      if (sel) { sel.selectAllChildren(input); sel.collapseToEnd(); }
      document.execCommand("insertText", false, " ");
      await sleep(300);
      document.execCommand("delete", false, null);
      await sleep(300);
      log("Prompt: forced React sync (space+delete)");
    }
    const visible = (input.textContent || "").length;
    log(`Prompt visible: ${visible} chars, success=${success}`);
    return success;
  }

  // ── Click send (verbatim) ────────────────────────────────────────────
  async function clickSend() {
    await sleep(1000);
    log("Waiting for send button to be ready...");
    for (let i = 0; i < 60; i++) {
      const btn = findSendButton();
      if (btn && !btn.disabled) {
        const tid = btn.getAttribute("data-testid");
        const lbl = btn.getAttribute("aria-label");
        const pre = snapshotAssistantCount();
        log(`Send button found (testid=${tid}, label=${lbl}), pre-send assistant count=${pre}, clicking ONCE...`);
        btn.click();
        await sleep(500);
        return true;
      }
      if (i > 0 && i % 5 === 0) {
        const inp = findPromptInput();
        if (inp) {
          inp.dispatchEvent(new InputEvent("input", { bubbles: true, inputType: "insertText" }));
          inp.dispatchEvent(new Event("change", { bubbles: true }));
        }
        log(`Send button still disabled... ${i * 0.5}s, retrying input event`);
      }
      await sleep(500);
    }
    const disabledSend = findSendButton(true);
    if (disabledSend) {
      log(`Force-clicking disabled send button`);
      disabledSend.disabled = false;
      disabledSend.removeAttribute("disabled");
      await sleep(100);
      disabledSend.click();
      await sleep(500);
      const inp = findPromptInput();
      const promptCleared = !inp || (inp.textContent || "").trim().length < 10;
      const stopBtn = document.querySelector("button[data-testid='stop-button']");
      if (promptCleared || stopBtn) { log("Force-click appears to have worked"); return true; }
    }
    const input = findPromptInput();
    if (input) {
      log("Send: trying Enter key...");
      input.focus();
      await sleep(100);
      for (const evtType of ["keydown", "keypress", "keyup"]) {
        input.dispatchEvent(new KeyboardEvent(evtType, {
          key: "Enter", code: "Enter", keyCode: 13, which: 13,
          bubbles: true, cancelable: true,
        }));
        await sleep(50);
      }
      await sleep(500);
      const remaining = (input.textContent || "").trim();
      if (remaining.length < 10) {
        log("Send: Enter key worked (prompt cleared)");
        return true;
      }
    }
    log("ERROR: cannot send after retries");
    return false;
  }

  // ── Response extraction ──────────────────────────────────────────────
  let sentPromptText = "";
  let postSendLines = new Set();
  let lastBottomScrollAt = 0;
  let lastBottomScrollLogAt = 0;
  let preSubmitAssistantCount = 0;
  function snapshotAssistantCount() {
    try {
      preSubmitAssistantCount = document.querySelectorAll(
        "[data-message-author-role='assistant']"
      ).length;
    } catch {
      preSubmitAssistantCount = 0;
    }
    return preSubmitAssistantCount;
  }
  function newAssistantCount() {
    try {
      return document.querySelectorAll("[data-message-author-role='assistant']").length;
    } catch {
      return 0;
    }
  }

  function clickScrollToBottomButton() {
    // ChatGPT shows a circular "scroll to bottom" button when the user has
    // scrolled up; while it is visible the stream-follow auto-scroll is paused.
    // We must click it to resume following the response as tokens stream.
    const selectors = [
      'button[aria-label*="Scroll to bottom" i]',
      'button[aria-label*="scroll" i]',
      'button[data-testid*="scroll-to-bottom" i]',
      'button[class*="scroll-to-bottom" i]',
    ];
    for (const sel of selectors) {
      try {
        for (const btn of document.querySelectorAll(sel)) {
          const rect = btn.getBoundingClientRect();
          if (rect.width > 0 && rect.height > 0 && !btn.disabled) {
            btn.click();
            return true;
          }
        }
      } catch {}
    }
    return false;
  }

  function scrollConversationToBottom(reason = "", force = false) {
    const now = Date.now();
    if (!force && now - lastBottomScrollAt < 5000) return false;
    lastBottomScrollAt = now;
    try {
      clickScrollToBottomButton();
      const main = document.querySelector("main");
      const messageNodes = main
        ? main.querySelectorAll("[data-message-author-role]")
        : [];
      const lastMessage = messageNodes.length ? messageNodes[messageNodes.length - 1] : null;
      const scrollables = [
        document.scrollingElement,
        document.documentElement,
        document.body,
        main,
      ];
      if (main) {
        for (const el of Array.from(main.querySelectorAll("div, section, article")).slice(-120)) {
          try {
            const style = window.getComputedStyle(el);
            if (/(auto|scroll)/.test(style.overflowY || "")
                && el.scrollHeight > el.clientHeight + 40) {
              scrollables.push(el);
            }
          } catch {}
        }
      }
      const seen = new Set();
      for (const el of scrollables) {
        if (!el || seen.has(el)) continue;
        seen.add(el);
        try { el.scrollTop = el.scrollHeight; } catch {}
      }
      try {
        window.scrollTo({ top: document.body.scrollHeight, behavior: "auto" });
      } catch {
        try { window.scrollTo(0, document.body.scrollHeight); } catch {}
      }
      try {
        if (lastMessage) lastMessage.scrollIntoView({ block: "end", inline: "nearest", behavior: "auto" });
      } catch {}
      for (const el of seen) {
        try { el.scrollTop = el.scrollHeight; } catch {}
      }
      if (now - lastBottomScrollLogAt >= 300000) {
        lastBottomScrollLogAt = now;
        log(`Viewport pinned to latest response${reason ? ` (${reason})` : ""}`);
      }
      return true;
    } catch {
      return false;
    }
  }

  function setSentPrompt(text) { sentPromptText = text; }

  function looksLikePromptEcho(text) {
    if (!sentPromptText || sentPromptText.length < 20) return false;
    const t = text.trim();
    if (/^(你说|You said)/i.test(t)) return true;
    const stripped = t
      .replace(/^(你说|You said)[：:]?\s*/i, "")
      .replace(/^main(\.pdf)?\s*/i, "")
      .replace(/^PDF\s*/i, "")
      .trim();
    const promptStart = sentPromptText.slice(0, 80).trim();
    if (stripped.length > 0
        && stripped.startsWith(promptStart)
        && stripped.length <= sentPromptText.length * 1.1) {
      return true;
    }
    if (t.length > 50
        && t.length < sentPromptText.length * 1.3
        && t.length > sentPromptText.length * 0.7) {
      const chunks = sentPromptText.match(/.{50}/g) || [];
      if (chunks.length > 10) {
        const hits = chunks.filter(c => t.includes(c)).length;
        if (hits / chunks.length > 0.8) return true;
      }
    }
    return false;
  }

  function capturePostSendState() {
    const main = document.querySelector("main");
    const text = main ? (main.innerText || "").trim() : "";
    postSendLines = new Set(text.split("\n").map(l => l.trim()).filter(l => l.length > 0));
    log(`Post-send captured: ${postSendLines.size} lines`);
  }

  function postSendNovelText(text) {
    if (postSendLines.size === 0) return "";
    const newLines = cleanText(text).split("\n").filter(l => {
      const t = l.trim();
      return t.length > 0 && !postSendLines.has(t) && !isChromeLine(t);
    });
    if (newLines.length < 2) return "";
    const joined = newLines.join("\n").trim();
    return joined.length >= 100 ? joined : "";
  }

  function hasPostSendNovelContent(text) {
    if (postSendLines.size === 0) return true;
    return postSendNovelText(text).length >= 100;
  }

  const CHROME_RE = [
    /^(进阶专业|ChatGPT\s*也可能会犯错|请核查重要信息|查看\s*Cookie|Cookie\s*首选项)/,
    /^(ChatGPT can make mistakes|Check important info)/,
    /^Extended\s*Pro$/i,
    /^(Deep research|Deep thinking|Reasoning)$/i,
    /^Thought for \d+/,
    /^(你说|You said|ChatGPT\s*说|ChatGPT\s*said)[：:]?\s*$/,
    /^(正在思考|正在搜索|Searching)/,
    /^main(\.pdf)?\s*$/,
    /^PDF\s*$/,
    /^(进阶专业模式|click to remove|Start dictation|Send prompt)/,
    /^(新建聊天|New chat|搜索聊天|Search chats|图片|Images)/,
    /^(查看方案|See plans|设置|Settings|帮助|Help)/,
    /^(获取根据保存的聊天量身定制的回复|Get responses tailored)/,
    /^(登录|Log in|注册|Sign up)/,
    /^(我们使用\s*cookie|We use cookies|管理\s*Cookie|Manage Cookies)/,
    /^(拒绝非必要|Reject non-essential|接受所有|Accept all)/,
    /^See Cookie Preferences/,
  ];
  const SSR_GARBAGE_RE = /window\.__oai_log|window\.__oai_SSR|requestAnimationFrame/;
  const SSR_LINE_RE = /window\.__oai_(log|SSR)\s*[=(]|requestAnimationFrame\s*\(/;

  function isChromeLine(t) {
    if (!t || t.length > 200) return false;
    return CHROME_RE.some(re => re.test(t));
  }

  function stableResponseKey(text) {
    const normalized = cleanText(text)
      .replace(/Thought for\s+\d+(?:\s*m\s*\d+\s*s|\s*s|\s+min)/gi, "Thought for <elapsed>")
      .replace(/\b\d{1,2}:\d{2}(?::\d{2})?\b/g, "<clock>")
      .replace(/\b(Pro thinking|Extended Pro|Reasoning…)\b/gi, "")
      .replace(/[ \t]+/g, " ")
      .replace(/\n{3,}/g, "\n\n")
      .trim();
    return normalized.length >= 5 ? normalized : text.trim();
  }

  function isSsrLine(t) {
    if (!t || t.length > 400) return false;
    return SSR_LINE_RE.test(t);
  }

  function cleanText(text) {
    return text.split("\n").filter(line => {
      const t = line.trim();
      if (!t) return true;
      if (isChromeLine(t)) return false;
      if (isSsrLine(t)) return false;
      return true;
    }).join("\n").trim();
  }

  function extractTextWithMath(el) {
    if (!el) return "";
    const clone = el.cloneNode(true);
    for (const ann of Array.from(
        clone.querySelectorAll('annotation[encoding="application/x-tex"]'))) {
      const latex = (ann.textContent || "").trim();
      if (!latex) continue;
      const katexOuter = ann.closest(".katex-display, .katex") || ann.parentElement;
      if (katexOuter) {
        const isDisplay = katexOuter.classList.contains("katex-display") ||
                          (katexOuter.parentElement &&
                           katexOuter.parentElement.classList.contains("katex-display"));
        const wrapped = isDisplay ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        katexOuter.replaceWith(document.createTextNode(wrapped));
      }
    }
    for (const mjx of Array.from(clone.querySelectorAll("mjx-container"))) {
      let latex = "";
      const mmlAnn = mjx.querySelector('annotation[encoding*="TeX"]');
      if (mmlAnn) latex = (mmlAnn.textContent || "").trim();
      if (!latex) latex = mjx.getAttribute("aria-label") || "";
      if (!latex) latex = mjx.getAttribute("data-latex") || "";
      if (latex) {
        const isDisplay = mjx.getAttribute("display") === "true" ||
                          mjx.getAttribute("data-display") === "block";
        const wrapped = isDisplay ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        mjx.replaceWith(document.createTextNode(wrapped));
      }
    }
    for (const mathEl of Array.from(
        clone.querySelectorAll("[data-math-tex], [data-tex], [data-latex]"))) {
      const latex = mathEl.getAttribute("data-math-tex") ||
                    mathEl.getAttribute("data-tex") ||
                    mathEl.getAttribute("data-latex") || "";
      if (latex) {
        const isBlock = mathEl.tagName.toLowerCase() === "div" ||
                        mathEl.getAttribute("display") === "block";
        const wrapped = isBlock ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        mathEl.replaceWith(document.createTextNode(wrapped));
      }
    }
    for (const math of Array.from(clone.querySelectorAll("math"))) {
      if (!math.isConnected) continue;
      const alttext = math.getAttribute("alttext") || "";
      if (alttext) math.replaceWith(document.createTextNode(` $${alttext}$ `));
    }
    return (clone.innerText || "").trim();
  }

  function stripSSRGarbage(text) {
    if (!text) return text;
    return text
      .replace(/I?window\.__oai_logHTML\?[^)]*\)\s*/g, "")
      .replace(/window\.__oai_SSR_HTML\s*=\s*window\.__oai_SSR_HTML\s*\|\|\s*Date\.now\(\)\s*;?\s*/g, "")
      .replace(/requestAnimationFrame\(\(function\(\)\{[^}]*\}\)\)\s*/g, "")
      .replace(/window\.__oai_logTTI\?[^)]*\)\s*/g, "")
      .replace(/window\.__oai_SSR_TTI\s*=\s*window\.__oai_SSR_TTI\s*\|\|\s*Date\.now\(\)\s*;?\s*/g, "")
      .replace(/ChatGPT said:/g, "")
      .trim();
  }

  function isSSROnly(text) {
    if (!text || text.length < 10) return false;
    const stripped = stripSSRGarbage(text);
    const lines = stripped.split("\n").filter(l => {
      const t = l.trim();
      return t.length > 0 && !isChromeLine(t) && !isSsrLine(t);
    });
    return lines.join("").trim().length < 20;
  }

  function stripThinkingPreamble(t) {
    return t
      .replace(/^ChatGPT said:\s*/i, "")
      .replace(/^I'm (?:checking|looking|searching|thinking|analyzing)[^.]*\.\s*/i, "")
      .replace(/^Thought for \d+[sm]\s*\d*[sm]?\s*/i, "")
      .trim();
  }

  function isSSRGarbage(text) {
    if (!text || text.length < 10) return false;
    if (text.length >= 500) return false;
    const ssrHits = (text.match(/window\.__oai_/g) || []).length;
    if (ssrHits >= 2) return true;
    const jsRatio = (text.match(/[{}();=]/g) || []).length / text.length;
    if (jsRatio > 0.15) return true;
    return false;
  }

  function extractAssistantOnly() {
    const main = document.querySelector("main");
    if (!main) return "";
    const els = main.querySelectorAll("[data-message-author-role='assistant']");
    if (els.length === 0) return "";
    const candidates = [];
    for (let i = els.length - 1; i >= 0; i--) {
      const text = cleanText(extractTextWithMath(els[i]));
      if (text.length >= 100 && !looksLikePromptEcho(text)) {
        candidates.push({ idx: i, text, len: text.length });
      }
    }
    if (candidates.length === 0) return "";
    candidates.sort((a, b) => b.idx - a.idx);
    return candidates[0].text;
  }

  function extractResponseText() {
    const main = document.querySelector("main");
    if (!main) return "";
    const fullText = extractTextWithMath(main);

    const assistantEls = main.querySelectorAll("[data-message-author-role='assistant']");
    for (let i = assistantEls.length - 1; i >= 0; i--) {
      const text = stripThinkingPreamble(cleanText(stripSSRGarbage(extractTextWithMath(assistantEls[i]))));
      if (text.length < 200) continue;
      if (looksLikePromptEcho(text)) continue;
      if (!hasPostSendNovelContent(text)) continue;
      if (isSSROnly(text)) continue;
      return text;
    }

    if (sentPromptText.length > 500) {
      const tailAnchor = sentPromptText.slice(-100).trim();
      let idx = fullText.lastIndexOf(tailAnchor);
      if (idx < 0 && tailAnchor.length > 50) idx = fullText.lastIndexOf(tailAnchor.slice(-50));
      if (idx >= 0) {
        const after = cleanText(fullText.slice(idx + tailAnchor.length));
        if (after.length > 100) return after;
      }
    }

    const novelText = postSendNovelText(fullText);
    if (novelText.length > 100 && !looksLikePromptEcho(novelText)) return novelText;

    const candidates = [];
    const allBlocks = main.querySelectorAll("div, article, section");
    for (const el of allBlocks) {
      const text = extractTextWithMath(el);
      if (text.length < 200) continue;
      candidates.push({ el, text, len: text.length });
    }
    candidates.sort((a, b) => b.len - a.len);
    for (const cand of candidates) {
      const cleaned = cleanText(cand.text);
      if (cleaned.length < 200) continue;
      const pageLen = fullText.length;
      if (cleaned.length > pageLen * 0.95 && candidates.length > 3) continue;
      if (looksLikePromptEcho(cleaned)) continue;
      if (!hasPostSendNovelContent(cleaned)) continue;
      if (sentPromptText.length > 500) {
        const promptStart = sentPromptText.slice(0, 200).trim();
        if (cleaned.startsWith(promptStart)
            && cleaned.length <= sentPromptText.length * 1.1) continue;
      }
      return cleaned;
    }

    const s0Selectors = [
      "[data-message-author-role='assistant']",
      "[data-testid*='conversation-turn']",
      "article",
      "div[class*='markdown']",
      "div[class*='prose']",
      "div.markdown",
      "[class*='agent-turn']",
    ];
    for (const sel of s0Selectors) {
      try {
        const els = document.querySelectorAll(sel);
        if (els.length === 0) continue;
        for (let i = els.length - 1; i >= 0; i--) {
          const text = extractTextWithMath(els[i]);
          const cleaned = cleanText(text);
          if (cleaned.length < 200) continue;
          if (looksLikePromptEcho(cleaned)) continue;
          if (!hasPostSendNovelContent(cleaned)) continue;
          if (sentPromptText.length > 30) {
            const ps = sentPromptText.slice(0, 40).trim();
            if (cleaned.startsWith(ps) && cleaned.length < sentPromptText.length * 1.2) continue;
          }
          return cleaned;
        }
      } catch {}
    }

    if (fullText.length < 100) return "";
    if (sentPromptText.length > 30) {
      for (const anchorLen of [80, 50, 30]) {
        const anchor = sentPromptText.slice(0, anchorLen).trim();
        const idx = fullText.indexOf(anchor);
        if (idx >= 0) {
          let endIdx = idx + sentPromptText.length;
          if (sentPromptText.length > 60) {
            const tail = sentPromptText.slice(-40).trim();
            const tailIdx = fullText.indexOf(tail, idx);
            if (tailIdx >= 0) endIdx = Math.max(endIdx, tailIdx + tail.length);
          }
          const after = cleanText(fullText.slice(endIdx));
          if (after.length > 100) return after;
        }
      }
    }

    return "";
  }

  function isStillGenerating() {
    const domSignal = !!(
      document.querySelector("button[aria-label='Stop generating']") ||
      document.querySelector("button[aria-label='Stop streaming']") ||
      document.querySelector("button[aria-label='停止生成']") ||
      document.querySelector("button[aria-label='停止流式传输']") ||
      document.querySelector("button[data-testid='stop-button']") ||
      document.querySelector("[class*='result-streaming']") ||
      document.querySelector("[class*='streaming']") ||
      document.querySelector("[class*='thinking']") ||
      document.querySelector("[class*='reasoning']") ||
      document.querySelector("[class*='progress']")
    );
    if (domSignal) return true;
    // Text-layer probe for ChatGPT 5.5 Pro reasoning indicators that don't
    // expose stable class hooks. The page text contains these literals while
    // the Pro reasoner is still thinking and before the visible answer
    // streams in.
    try {
      const main = document.querySelector("main");
      if (!main) return false;
      const txt = main.innerText || "";
      // "Pro thinking" — ChatGPT 5.5 Pro reasoning state preamble
      // "Extended Pro" — appears in reasoner footer DURING reasoning, not after
      // "Thought for" — only appears AFTER reasoning completes (post-think)
      // We treat the page as still generating if the reasoning preamble is
      // present AND the post-think marker "Thought for" is NOT yet visible,
      // since "Thought for X min Ys" appears once reasoning is done and the
      // answer starts streaming.
      const proPreamble = /Pro thinking|Extended Pro|Reasoning…/i.test(txt);
      const postThink = /Thought for\s+\d+(?:\s*m\s*\d+\s*s|\s*s|\s+min)/i.test(txt);
      if (proPreamble && !postThink) return true;
    } catch {}
    return false;
  }

  async function waitForResponse(task_id, minResponseLength = DEFAULT_MIN_RESPONSE_LENGTH) {
    log(`Waiting for ChatGPT response (pre-send assistant count was ${preSubmitAssistantCount})...`);
    const startTime = Date.now();
    let lastResponseText = "";
    let lastStableKey = "";
    let stableCount = 0;
    let lastLogTime = 0;
    let lastHeartbeat = 0;
    let countIncreasedLogged = false;
    while (Date.now() - startTime < MAX_WAIT) {
      await sleep(STABLE_INTERVAL);
      scrollConversationToBottom("wait");
      await sleep(500);
      const curCount = newAssistantCount();
      let responseText = (curCount > preSubmitAssistantCount)
        ? extractAssistantOnly()    // count increased: take the LAST assistant message only
        : "";                       // count not yet increased: don't even consider stability
      if (curCount > preSubmitAssistantCount && responseText.length < 5) {
        scrollConversationToBottom("empty-after-count-increase", true);
        await sleep(1000);
        responseText = extractAssistantOnly();
      }
      if (curCount > preSubmitAssistantCount && !countIncreasedLogged) {
        log(`new assistant message detected (count ${preSubmitAssistantCount} → ${curCount})`);
        countIncreasedLogged = true;
      }
      const generating = isStillGenerating();
      const elapsed = Math.floor((Date.now() - startTime) / 1000);
      const mainLen = (document.querySelector("main")?.innerText || "").length;
      const nowMs = Date.now();
      if (task_id && nowMs - lastHeartbeat >= 60000) {
        lastHeartbeat = nowMs;
        let ack = null;
        try {
          ack = await serverPost("/ack", {
            task_id,
            agent_id: agentId(),
            heartbeat: true,
            metrics: {
              elapsed_seconds: elapsed,
              extracted_chars: responseText.length,
              page_chars: mainLen,
              stable_count: stableCount,
              generating,
              url_tail: window.location.href.slice(-60),
            },
          });
        } catch {}
        if (ack && ack.status === "cancelled") {
          throw new Error(`Task cancelled by server: ${task_id}`);
        }
      }
      if (elapsed - lastLogTime >= 300) {
        lastLogTime = elapsed;
        log(`Wait: ${elapsed}s, extracted=${responseText.length}, page=${mainLen}, stable=${stableCount}, gen=${generating}, url=${window.location.href.slice(-30)}`);
      }
      if (responseText.length >= 5) {
        if (looksLikePromptEcho(responseText)) {
          if (stableCount === 0) log(`Prompt echo detected (${responseText.length} chars) — waiting`);
          stableCount = 0; lastResponseText = ""; lastStableKey = ""; continue;
        }
        if (isSSRGarbage(responseText)) {
          responseText = stripSSRGarbage(responseText);
          if (isSSROnly(responseText)) {
            if (stableCount === 0) log(`SSR-only content (${responseText.length} chars) — page hydrating, waiting`);
            stableCount = 0; lastResponseText = ""; lastStableKey = ""; continue;
          }
          log(`Stripped SSR fragments, ${responseText.length} chars remain`);
        }
        const stableKey = stableResponseKey(responseText);
        if (stableKey === lastStableKey) {
          stableCount++;
          lastResponseText = responseText;
          let minChecks;
          if (responseText.length >= 5000) minChecks = STABLE_CHECKS;
          else if (responseText.length >= minResponseLength) minChecks = STABLE_CHECKS + 2;
          else minChecks = STABLE_CHECKS * 3;
          const stableEnough = stableCount >= minChecks && !generating;
          const stableOverride = stableCount >= minChecks + 3;
          if (stableEnough || stableOverride) {
            log(`Response complete: ${responseText.length} chars (stable ${stableCount * STABLE_INTERVAL / 1000}s, gen=${generating})`);
            return responseText;
          }
        } else {
          stableCount = 0;
          lastResponseText = responseText;
          lastStableKey = stableKey;
        }
      } else if (generating) {
        stableCount = 0;
      }
    }
    const timeoutNote = `\n\n[TIMEOUT after ${Math.floor(MAX_WAIT / 1000)}s; returning the latest stable partial response.]`;
    log(`TIMEOUT (${MAX_WAIT/1000}s), returning partial: ${lastResponseText.length} chars`);
    return lastResponseText ? `${lastResponseText}${timeoutNote}` : timeoutNote.trim();
  }

  // ── Process a task ───────────────────────────────────────────────────
  async function processTask(task) {
    const { task_id, prompt, conversation_url, is_followup, conversation_id, re_extract, pdf_base64, pdf_name, min_response_length } = task;
    const minResponseLength = Number.isFinite(Number(min_response_length))
      ? Number(min_response_length)
      : DEFAULT_MIN_RESPONSE_LENGTH;
    busy = true;
    updatePanel();

    if (!isInsideBioRealityProject()) {
      navigateTaskBackToProject(task, "outside project before task");
      return;
    }

    if (re_extract) {
      log(`=== Task: ${task_id} [RE-EXTRACT] conv=${(conversation_id || "").slice(0, 12)} ===`);
      try {
        const pinnedConv = pinToProject(conversation_url);
        if (pinnedConv && !window.location.href.startsWith(pinnedConv)) {
          tabSet("navigating", true);
          tabSet("nav_task_id", task_id);
          saveTaskState(task);
          setTaskPhase("navigating");
          log(`Navigating to ${pinnedConv.slice(-60)} for re-extract ...`);
          busy = false;
          updatePanel();
          window.location.href = pinnedConv;
          return;
        }
        try { await serverPost("/ack", { task_id, agent_id: agentId() }); } catch {}
        await sleep(3000); // settle DOM
        scrollConversationToBottom("re-extract", true);
        await sleep(1000);
        if (prompt) setSentPrompt(prompt);
        let response = extractAssistantOnly();
        if (!response || response.length < 100) {
          log(`re-extract: assistant-only got ${response?.length || 0} chars; falling back to extractResponseText`);
          response = extractResponseText();
        } else {
          log(`re-extract: assistant-only got ${response.length} chars`);
        }
        if (!response || response.length < 100) {
          throw new Error(`re-extract: nothing meaningful (${response?.length || 0} chars)`);
        }
        const chatUrl = currentChatUrl();
        await serverPost("/result", {
          task_id, response, chatgpt_url: chatUrl,
          agent_id: agentId(), model: task.model || "unknown",
        });
        log(`DONE (re-extract): ${task_id} (${response.length} chars)`);
        clearTaskState();
        setInFlightTaskId("");
      } catch (err) {
        log(`ERROR (re-extract): ${err.message}`);
        try {
          await serverPost("/result", {
            task_id, response: `ERROR (re-extract): ${err.message}`,
            chatgpt_url: currentChatUrl(), agent_id: agentId(),
            model: task.model || "unknown",
          });
        } catch {}
        clearTaskState();
        setInFlightTaskId("");
      } finally {
        busy = false;
        updatePanel();
      }
      return;
    }

    const onConvPage = /\/c\/[a-f0-9-]{6,}/.test(window.location.href);
    if (getInFlightTaskId() === task_id && onConvPage) {
      log(`=== Task: ${task_id} [RESUMING on existing chat ${currentChatUrl().slice(-40)}] ===`);
      try { await serverPost("/ack", { task_id, agent_id: agentId() }); } catch {}
      setTaskPhase("processing");
      setSentPrompt(prompt);
      scrollConversationToBottom("resume", true);
      await sleep(500);
      capturePostSendState();
      try {
        const response = await waitForResponse(task_id, minResponseLength);
        if (!response || response.length < 5) {
          throw new Error(`Resumed wait got no response (${response?.length || 0} chars)`);
        }
        const chatUrl = currentChatUrl();
        log(`Resumed chat URL captured: ${chatUrl.slice(-50) || "(none)"}`);
        await serverPost("/result", {
          task_id, response, chatgpt_url: chatUrl,
          agent_id: agentId(), model: task.model || "unknown",
        });
        log(`DONE (resumed): ${task_id} (${response.length} chars)`);
        clearTaskState();
        setInFlightTaskId("");
      } catch (err) {
        log(`ERROR (resumed): ${err.message}`);
        try {
          await serverPost("/result", {
            task_id, response: `ERROR (resumed): ${err.message}`,
            chatgpt_url: currentChatUrl(), agent_id: agentId(),
            model: task.model || "unknown",
          });
        } catch {}
        clearTaskState();
        setInFlightTaskId("");
      } finally {
        busy = false;
        updatePanel();
      }
      return;
    }

    log(`=== Task: ${task_id} ${is_followup ? "[FOLLOW-UP]" : "[NEW]"} conv=${(conversation_id || "").slice(0, 12)} ===`);

    try {
      const targetUrl = (is_followup && conversation_url) ? pinToProject(conversation_url) : null;
      const needNavToConv = targetUrl && !window.location.href.startsWith(targetUrl);
      const needNavToFresh = !targetUrl && !isOnNewChatPage();

      if (needNavToFresh) {
        log(`Need fresh chat. Current URL: ${window.location.href.slice(-60)}`);
        const ok = await clickNewChatButton();
        if (ok) {
          log(`Clicked New Chat button; on fresh chat now.`);
          // No reload — keep going in same script instance
        } else {
          log(`No New Chat button found; falling back to URL navigation`);
          tabSet("navigating", true);
          tabSet("nav_task_id", task_id);
          saveTaskState(task);
          setTaskPhase("navigating");
          busy = false;
          updatePanel();
          const m = window.location.pathname.match(/^(\/g\/g-p-[a-zA-Z0-9_-]+)/);
          const aid = agentId();
          const flagMatch = aid.match(/^bio_(\d+)$/);
          const bioFlag = flagMatch ? flagMatch[1] : "1";
          const fallbackUrl = `${BIOREALITY_PROJECT_HOME}${bioFlag ? `?bio=${encodeURIComponent(bioFlag)}` : ""}`;
          log(`fallback URL: ${fallbackUrl} (agentId=${aid})`);
          window.location.href = fallbackUrl;
          return;
        }
      } else if (needNavToConv) {
        tabSet("navigating", true);
        tabSet("nav_task_id", task_id);
        saveTaskState(task);
        setTaskPhase("navigating");
        log(`Navigating to existing conv ${(targetUrl || "").slice(-60)} ...`);
        busy = false;
        updatePanel();
        window.location.href = targetUrl;
        return;
      }

      if (!isInsideBioRealityProject()) {
        navigateTaskBackToProject(task, "navigation left project");
        return;
      }

      // ACK
      if (!isForegroundReady()) {
        log(`Foreground gate not ready (${foregroundState()})`);
      }
      try { await serverPost("/ack", { task_id, agent_id: agentId() }); } catch {}
      setTaskPhase("processing");
      setInFlightTaskId(task_id);
      saveTaskState(task);

      // Wait for prompt input. Bumped to 90s — ChatGPT 5.5 fresh chat can be
      // slow to hydrate, especially after a New Chat button click that
      // unmounts and remounts the composer. Log every 15s for visibility.
      let retries = 0;
      while (!findPromptInput() && retries < 90) {
        await sleep(1000);
        retries++;
        if (retries > 0 && retries % 15 === 0) {
          log(`Still waiting for prompt input... ${retries}s, url=${window.location.href.slice(-50)}`);
        }
      }
      if (!findPromptInput()) {
        throw new Error(`Prompt input not found after 90s (url=${window.location.href})`);
      }
      log(`Page ready (${is_followup ? "existing conv" : "fresh chat"}) after ${retries}s`);

      if (!is_followup && pdf_base64) {
        try {
          const ok = await uploadPDF(pdf_base64, pdf_name || "main.pdf");
          if (!ok) log("PDF upload failed — proceeding without PDF context");
        } catch (e) {
          log(`PDF upload exception: ${e.message} — proceeding without PDF`);
        }
      }

      // Enter prompt
      const entered = await enterPrompt(prompt);
      if (!entered) throw new Error("Failed to enter prompt text");
      setSentPrompt(prompt);

      // Wait for send button
      log("Waiting for send button to enable...");
      let sendReady = false;
      for (let i = 0; i < 30; i++) {
        const btn = findSendButton();
        if (btn && !btn.disabled) { sendReady = true; log(`Send ready after ${i}s`); break; }
        await sleep(1000);
      }
      if (!sendReady) log("WARN: send still disabled after 30s, will force-click");

      const urlBefore = window.location.href;
      const sent = await clickSend();
      if (!sent) throw new Error("Failed to click send");

      // For new chat: wait for URL change to /c/<id>
      // For follow-up: URL should NOT change (we stay in same /c/<id>)
      log(`Sent. urlBefore=${urlBefore.slice(-40)}`);
      if (!is_followup) {
        let urlChanged = false;
        for (let i = 0; i < 60; i++) {
          await sleep(1000);
          if (window.location.href !== urlBefore) {
            urlChanged = true;
            log(`URL changed to: ${window.location.href.slice(-40)}`);
            break;
          }
          if (isStillGenerating()) { log("Generation detected (same page)"); break; }
        }
        if (!urlChanged && !isStillGenerating()) {
          log("WARN: URL did not change and no generation after 60s");
        }
      } else {
        // For follow-up: just wait for generation to start
        for (let i = 0; i < 30; i++) {
          await sleep(1000);
          if (isStillGenerating()) { log("Follow-up generation started"); break; }
        }
      }

      await sleep(5000); // settle DOM
      scrollConversationToBottom("post-send", true);
      await sleep(500);
      capturePostSendState();
      const response = await waitForResponse(task_id, minResponseLength);

      if (!response || response.length < 5) {
        throw new Error(`Response too short or empty (${response?.length || 0} chars)`);
      }

      const chatUrl = currentChatUrl();
      log(`Chat URL captured: ${chatUrl.slice(-50) || "(none)"}`);

      await serverPost("/result", {
        task_id,
        response,
        chatgpt_url: chatUrl,
        agent_id: agentId(),
        model: task.model || "unknown",
      });
      log(`DONE: ${task_id} (${response.length} chars)`);
      clearTaskState();
      setInFlightTaskId("");
    } catch (err) {
      log(`ERROR: ${err.message}`);
      try {
        await serverPost("/result", {
          task_id, response: `ERROR: ${err.message}`,
          chatgpt_url: currentChatUrl(),
          agent_id: agentId(), model: task.model || "unknown",
        });
      } catch {}
      clearTaskState();
      setInFlightTaskId("");
    } finally {
      busy = false;
      updatePanel();
    }
  }

  function agentId() {
    try {
      if (AGENT_ID) {
        sessionStorage.setItem("bio_agent_id", AGENT_ID);
        return AGENT_ID;
      }
      const m = window.location.search.match(/[?&]bio=([^&]+)/);
      if (m) {
        const id = `bio_${m[1]}`;
        sessionStorage.setItem("bio_agent_id", id);
        return id;
      }
      let stored = sessionStorage.getItem("bio_agent_id");
      if (stored) return stored;
      stored = `bio_${Math.floor(Math.random() * 9000) + 1000}_${Date.now().toString(36).slice(-4)}`;
      sessionStorage.setItem("bio_agent_id", stored);
      return stored;
    } catch {
      // Private mode / sessionStorage disabled — fall back to window.name
      if (!window.name || !window.name.startsWith("bio_")) {
        const m = window.location.search.match(/[?&]bio=([^&]+)/);
        window.name = m
          ? `bio_${m[1]}`
          : `bio_${Math.floor(Math.random() * 9000) + 1000}_${Date.now().toString(36).slice(-4)}`;
      }
      return window.name;
    }
  }

  function tabSet(k, v) { return GM_setValue(`${agentId()}_${k}`, v); }
  function tabGet(k, d) { return GM_getValue(`${agentId()}_${k}`, d); }

  function bioFlagForAgent() {
    const flagMatch = agentId().match(/^bio_(\d+)$/);
    return flagMatch ? flagMatch[1] : (bioFlagFromUrl() || "1");
  }

  function projectEntryUrlForAgent() {
    const flag = bioFlagForAgent();
    return `${BIOREALITY_PROJECT_HOME}${flag ? `?bio=${encodeURIComponent(flag)}` : ""}`;
  }

  function navigateTaskBackToProject(task, reason) {
    const taskId = (task && task.task_id) || "";
    const target = /\/c\/[a-f0-9-]{6,}/.test(window.location.href)
      ? pinToProject(window.location.href)
      : projectEntryUrlForAgent();
    tabSet("navigating", true);
    tabSet("nav_task_id", taskId);
    if (task) saveTaskState(task);
    setTaskPhase("navigating");
    log(`${reason}; navigating to BioReality chat ${target.slice(-80)}`);
    busy = false;
    updatePanel();
    window.location.href = target;
  }

  // ── Main loop ────────────────────────────────────────────────────────
  function _readActive() {
    try { return sessionStorage.getItem("bio_active") === "1" && isInsideBioRealityProject(); }
    catch { return false; }
  }

  function enforceProjectBeforePolling() {
    if (isInsideBioRealityProject()) return false;
    if (window.location.search.includes("bio=")) {
      const target = projectEntryUrl();
      log(`BioReality chat required; navigating to ${target}`);
      window.location.href = target;
      return true;
    }
    try { sessionStorage.setItem("bio_active", "0"); } catch {}
    active = false;
    log("Outside BioReality chat; polling paused");
    updatePanel();
    return true;
  }

  async function pollLoop() {
    while (true) {
      active = _readActive();
      if (active && !busy) {
        if (enforceProjectBeforePolling()) {
          await sleep(POLL_INTERVAL);
          continue;
        }
        try {
          const task = await serverGet(`/task?agent=${encodeURIComponent(agentId())}`);
          if (task && task.task_id && task.status !== "idle") {
            if (!_readActive()) {
              log("Task available but PAUSED — skipping");
            } else {
              await processTask(task);
            }
          }
        } catch (err) {
          if (logHistory.length === 0 || !logHistory[logHistory.length-1].includes("unreachable")) {
            log(`Server unreachable (${SERVER})`);
          }
        }
      }
      await sleep(POLL_INTERVAL);
    }
  }

  // ── Bootstrap ────────────────────────────────────────────────────────
  async function init() {
    log(`BioReality Oracle Bridge ${SCRIPT_VERSION} loaded — ${active ? "ACTIVE" : "PAUSED"} — agent=${agentId()}`);

    const phase = getTaskPhase();
    const navTaskId = tabGet("nav_task_id", "");
    const bioNav = tabGet("navigating", false);
    const urlHasFlag = window.location.search.includes("bio=");
    const inFlightId = getInFlightTaskId();
    const inFlightAgeMin = Math.floor(getInFlightAgeMs() / 60000);
    const storedActive = (() => {
      try { return sessionStorage.getItem("bio_active") === "1"; }
      catch { return false; }
    })();

    if (urlHasFlag && !isInsideBioRealityProject()) {
      const target = projectEntryUrl();
      log(`BioReality chat required; navigating to ${target}`);
      window.location.href = target;
      return;
    }

    if ((inFlightId || storedActive) && ensureInProject()) return;

    if (inFlightId && inFlightAgeMin > 180) {
      log(`Stale in-flight ${inFlightId} (${inFlightAgeMin}m old) — clearing`);
      setInFlightTaskId("");
      clearTaskState();
    }

    if (inFlightId && /\/c\/[a-f0-9-]/.test(window.location.href)) {
      log(`Detected mid-task reload on /c/<uuid>; in-flight=${inFlightId} (${inFlightAgeMin}m). pollLoop will resume.`);
      try {
        await serverPost("/pin-conv-url", {
          task_id: inFlightId,
          chatgpt_url: currentChatUrl(),
          agent_id: agentId(),
        });
      } catch {}
    }

    if (phase === "navigating" && navTaskId && (bioNav || urlHasFlag)) {
      log(`Resuming after navigation for task: ${navTaskId}`);
      tabSet("nav_task_id", "");
      tabSet("navigating", false);
      const savedTask = loadTaskState();
      clearTaskState();

      if (urlHasFlag) {
        const cleanUrl = window.location.href.replace(/[?&]bio=[^&]+/, "").replace(/\?$/, "");
        history.replaceState(null, "", cleanUrl);
      }

      await sleep(3000);

      // Prefer the saved task (preserves is_followup + conversation context).
      // Fall back to re-fetching if state was lost.
      let task = savedTask;
      if (!task || !task.task_id) {
        try {
          task = await serverGet(`/task?agent=${encodeURIComponent(agentId())}`);
        } catch (e) { log(`Re-fetch failed: ${e.message}`); }
      }
      if (task && task.task_id && task.status !== "idle") {
        log(`Resumed task: ${task.task_id} prompt=${task.prompt?.length || 0} chars followup=${!!task.is_followup}`);
        await processTask(task);
      } else {
        log("WARN: no task to resume after navigation");
      }
    } else if (phase === "navigating") {
      log("Clearing stale navigation state (user browsing, not bio)");
      tabSet("nav_task_id", "");
      tabSet("navigating", false);
      clearTaskState();
    }

    pollLoop();
  }

  if (document.readyState === "complete") setTimeout(init, 2000);
  else window.addEventListener("load", () => setTimeout(init, 2000));
})();
