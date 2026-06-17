#!/usr/bin/env node

import http from "node:http";
import path from "node:path";
import { readFile, stat } from "node:fs/promises";
import { pathToFileURL } from "node:url";

const DEFAULT_CDP = "http://127.0.0.1:9222";
const DEFAULT_HOST = "127.0.0.1";
const DEFAULT_PORT = 8765;
const DEFAULT_CHAT_URL_FRAGMENT = "6a32835f-e560-83ee-a061-8fe3b0ddfbb9";
const LOOPBACK_HOSTS = new Set(["127.0.0.1", "localhost", "::1", "[::1]"]);
const ASK_WAIT_FLOORS = {
  minResponseChars: 80,
  minWaitAfterFirstMs: 15000,
  stableMs: 5000,
};
const ATTACH_WAIT_FLOORS = {
  waitMs: 120000,
  stableMs: 3000,
};

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 0; i < argv.length; i += 1) {
    const token = argv[i];
    if (!token.startsWith("--")) {
      args._.push(token);
      continue;
    }
    const key = token.slice(2);
    const value = argv[i + 1] && !argv[i + 1].startsWith("--") ? argv[++i] : "true";
    args[key] = value;
  }
  return args;
}

async function jsonFetch(url, init) {
  const response = await fetch(url, init);
  if (!response.ok) {
    throw new Error(`${response.status} ${response.statusText}: ${url}`);
  }
  return response.json();
}

export function selectAuthorizedPage(targets, { cdp = DEFAULT_CDP, conversationId = DEFAULT_CHAT_URL_FRAGMENT } = {}) {
  if (!conversationId || conversationId === "true") {
    throw new Error("Authorized ChatGPT conversation fragment is required");
  }
  const page = targets
    .filter((target) => target.type === "page")
    .find((target) => isAuthorizedChatUrl(target.url, conversationId));
  if (!page) {
    throw new Error(`Authorized ChatGPT conversation not found at ${cdp}: ${conversationId}`);
  }
  if (!page.webSocketDebuggerUrl) {
    throw new Error(`Authorized ChatGPT conversation has no CDP websocket: ${page.url || page.id || "unknown"}`);
  }
  assertLoopbackUrl(page.webSocketDebuggerUrl, "CDP websocket");
  return page;
}

export function isAuthorizedChatUrl(rawUrl, conversationId = DEFAULT_CHAT_URL_FRAGMENT) {
  try {
    const url = new URL(rawUrl || "");
    const host = url.hostname.toLowerCase();
    const parts = url.pathname.split("/").filter(Boolean);
    const conversationIndex = parts.indexOf("c");
    return (
      (host === "chatgpt.com" || host === "www.chatgpt.com") &&
      conversationIndex >= 0 &&
      parts[conversationIndex + 1] === conversationId
    );
  } catch {
    return false;
  }
}

export function assertLoopbackUrl(rawUrl, label) {
  const url = new URL(rawUrl);
  if (!LOOPBACK_HOSTS.has(url.hostname)) {
    throw new Error(`Refusing non-loopback ${label}: ${rawUrl}`);
  }
}

export function normalizePdfAttachOptions(options = {}) {
  return {
    pdfPath: typeof options.pdfPath === "string" && options.pdfPath.trim() ? options.pdfPath.trim() : "",
    attachWaitMs: floorNumber(options.attachWaitMs, ATTACH_WAIT_FLOORS.waitMs, ATTACH_WAIT_FLOORS.waitMs),
    attachStableMs: floorNumber(options.attachStableMs, ATTACH_WAIT_FLOORS.stableMs, ATTACH_WAIT_FLOORS.stableMs),
  };
}

export async function resolveLocalPdfPath(rawPath) {
  if (!rawPath || typeof rawPath !== "string") return "";
  const resolved = path.resolve(rawPath);
  if (!resolved.toLowerCase().endsWith(".pdf")) {
    throw new Error(`PDF attachment must have .pdf extension: ${rawPath}`);
  }
  const info = await stat(resolved);
  if (!info.isFile()) {
    throw new Error(`PDF attachment path is not a file: ${resolved}`);
  }
  if (info.size <= 0) {
    throw new Error(`PDF attachment is empty: ${resolved}`);
  }
  return resolved;
}

async function findPage({ cdp = DEFAULT_CDP } = {}) {
  assertLoopbackUrl(cdp, "CDP endpoint");
  const targets = await jsonFetch(`${cdp}/json/list`);
  return selectAuthorizedPage(targets, { cdp, conversationId: DEFAULT_CHAT_URL_FRAGMENT });
}

async function withPage(fn, options = {}) {
  const page = await findPage(options);
  const ws = new WebSocket(page.webSocketDebuggerUrl);
  let nextId = 0;
  const pending = new Map();

  ws.onmessage = (event) => {
    const message = JSON.parse(event.data);
    if (message.id && pending.has(message.id)) {
      pending.get(message.id)(message);
      pending.delete(message.id);
    }
  };

  await new Promise((resolve, reject) => {
    ws.onopen = resolve;
    ws.onerror = reject;
  });

  const call = (method, params = {}) =>
    new Promise((resolve) => {
      const id = ++nextId;
      pending.set(id, resolve);
      ws.send(JSON.stringify({ id, method, params }));
    });

  try {
    await call("Runtime.enable");
    await call("Page.enable");
    await call("DOM.enable");
    return await fn({ page, call });
  } finally {
    ws.close();
  }
}

async function evaluate(call, expression, timeout = 30000) {
  const result = await call("Runtime.evaluate", {
    expression,
    returnByValue: true,
    awaitPromise: true,
    timeout,
  });
  if (result.error) {
    throw new Error(JSON.stringify(result.error));
  }
  if (result.result?.exceptionDetails) {
    throw new Error(result.result.exceptionDetails.text || "Runtime.evaluate exception");
  }
  return result.result?.result?.value;
}

function readExpression() {
  return `(() => {
    const text = document.body ? document.body.innerText : "";
    const turns = Array.from(document.querySelectorAll("[data-message-author-role]")).map((el, i) => ({
      i,
      role: el.getAttribute("data-message-author-role"),
      text: el.innerText || ""
    }));
    const modal = document.querySelector("[data-testid*='modal'], [id*='modal']");
    return {
      title: document.title,
      url: location.href,
      textLen: text.length,
      turnCount: turns.length,
      turns,
      modalText: modal ? (modal.innerText || "").slice(0, 1000) : ""
    };
  })()`;
}

async function readChat(options = {}) {
  return withPage(async ({ page, call }) => {
    const value = await evaluate(call, readExpression());
    return { target: { title: page.title, url: page.url, id: page.id }, ...value };
  }, options);
}

function floorNumber(value, fallback, floor) {
  const parsed = Number(value ?? fallback);
  if (!Number.isFinite(parsed)) return floor;
  return Math.max(floor, parsed);
}

export function normalizeAskWaitOptions(options = {}) {
  return {
    waitMs: Number(options.waitMs || 600000),
    minResponseChars: floorNumber(options.minResponseChars, ASK_WAIT_FLOORS.minResponseChars, ASK_WAIT_FLOORS.minResponseChars),
    minWaitAfterFirstMs: floorNumber(
      options.minWaitAfterFirstMs,
      ASK_WAIT_FLOORS.minWaitAfterFirstMs,
      ASK_WAIT_FLOORS.minWaitAfterFirstMs,
    ),
    stableMs: floorNumber(options.stableMs, ASK_WAIT_FLOORS.stableMs, ASK_WAIT_FLOORS.stableMs),
  };
}

export async function waitForStableAssistant(call, beforeCount, waitMs, options = {}) {
  const deadline = Date.now() + waitMs;
  const minResponseChars = Number(options.minResponseChars || 80);
  const minWaitAfterFirstMs = Number(options.minWaitAfterFirstMs || 15000);
  const stableMs = Number(options.stableMs || 5000);
  let last = null;
  let stableSince = 0;
  let firstTextAt = 0;

  while (Date.now() < deadline) {
    const state = await evaluate(call, readExpression());
    const assistantCount = state.turns.filter((turn) => turn.role === "assistant").length;
    const lastAssistant = [...state.turns].reverse().find((turn) => turn.role === "assistant");
    const stopVisible = await evaluate(
      call,
      `(() => !!document.querySelector("button[data-testid='stop-button'], button[aria-label*='Stop'], button[aria-label*='停止']"))()`,
      5000,
    );

    if (assistantCount > beforeCount && lastAssistant?.text) {
      if (!firstTextAt) firstTextAt = Date.now();
      if (lastAssistant.text === last && !stopVisible) {
        if (!stableSince) stableSince = Date.now();
        const longEnough = lastAssistant.text.trim().length >= minResponseChars;
        const waitedAfterFirst = Date.now() - firstTextAt >= minWaitAfterFirstMs;
        if (Date.now() - stableSince > stableMs && longEnough && waitedAfterFirst) return state;
      } else {
        last = lastAssistant.text;
        stableSince = 0;
      }
    }
    await new Promise((resolve) => setTimeout(resolve, 1500));
  }

  throw new Error(`Timed out waiting for assistant response after ${waitMs}ms`);
}

function composerStateExpression() {
  return `(() => {
    const box = document.querySelector("#prompt-textarea, textarea[data-testid='prompt-textarea'], div[contenteditable='true'][role='textbox']");
    const buttons = Array.from(document.querySelectorAll("button"));
    const send = document.querySelector("button[data-testid='send-button']") ||
      buttons.find((button) => /send|发送/i.test(button.getAttribute("aria-label") || "")) ||
      buttons.find((button) => (button.innerText || "").trim() === "Send");
    const stop = document.querySelector("button[data-testid='stop-button'], button[aria-label*='Stop'], button[aria-label*='停止']");
    const turns = Array.from(document.querySelectorAll("[data-message-author-role]")).map((el) => ({
      role: el.getAttribute("data-message-author-role"),
      text: el.innerText || ""
    }));
    return {
      userCount: turns.filter((turn) => turn.role === "user").length,
      assistantCount: turns.filter((turn) => turn.role === "assistant").length,
      promptText: box ? (box.value || box.innerText || "").trim().slice(0, 1000) : "",
      sendExists: !!send,
      sendEnabled: !!send && !send.disabled && send.getAttribute("aria-disabled") !== "true",
      stopVisible: !!stop
    };
  })()`;
}

export async function waitForPromptSubmitted(call, beforeUserCount, sentState, waitMs = 15000) {
  const deadline = Date.now() + waitMs;
  let lastState = null;
  while (Date.now() < deadline) {
    const state = await evaluate(call, composerStateExpression(), 5000);
    lastState = state;
    if (Number(state.userCount || 0) > Number(beforeUserCount || 0)) return state;
    if (!state.promptText && state.stopVisible) return state;
    await new Promise((resolve) => setTimeout(resolve, 500));
  }
  throw new Error(`Prompt was not submitted: sent=${JSON.stringify(sentState)} composer=${JSON.stringify(lastState)}`);
}

function attachmentStateExpression() {
  return `(() => {
    const bodyText = document.body ? document.body.innerText : "";
    const attachmentNodes = Array.from(document.querySelectorAll(
      "[data-testid*='attachment'], [class*='attachment'], [class*='uploaded'], [aria-label*='attachment'], [aria-label*='file']"
    ));
    const uploading = !!(
      document.querySelector("[class*='uploading'], [data-testid*='uploading'], [aria-label*='uploading']") ||
      /uploading|processing file|attaching|正在上传|上传中/i.test(bodyText)
    );
    const send = document.querySelector("button[data-testid='send-button']") ||
      Array.from(document.querySelectorAll("button")).find((button) => /send|发送/i.test(button.getAttribute("aria-label") || ""));
    return {
      attachmentCount: attachmentNodes.length,
      attachmentText: attachmentNodes.map((node) => (node.innerText || node.getAttribute("aria-label") || "")).join("\\n").slice(0, 1000),
      uploading,
      sendEnabled: !!send && !send.disabled && send.getAttribute("aria-disabled") !== "true"
    };
  })()`;
}

async function queryFileInputNodeId(call) {
  const documentResult = await call("DOM.getDocument", { depth: -1, pierce: true });
  const rootId = documentResult.result?.root?.nodeId;
  if (!rootId) throw new Error("Cannot inspect DOM root for file input");
  for (const selector of ["input[type='file'][accept*='pdf']", "input[type='file']"]) {
    const found = await call("DOM.querySelectorAll", { nodeId: rootId, selector });
    const nodeIds = found.result?.nodeIds || [];
    if (nodeIds.length > 0) return nodeIds[nodeIds.length - 1];
  }
  return 0;
}

async function clickAttachButton(call) {
  return evaluate(
    call,
    `(() => {
      const buttons = Array.from(document.querySelectorAll("button"));
      const attach = document.querySelector("button[data-testid='composer-attach-button']") ||
        buttons.find((button) => /attach|file|添加|文件|plus|上传/i.test(
          [button.getAttribute("aria-label") || "", button.innerText || "", button.title || ""].join(" ")
        ));
      if (!attach) return { ok: false, reason: "no_attach_button" };
      if (attach.disabled || attach.getAttribute("aria-disabled") === "true") {
        return { ok: false, reason: "attach_disabled" };
      }
      attach.click();
      return { ok: true };
    })()`,
    5000,
  );
}

async function waitForAttachmentReady(call, beforeState, waitMs, stableMs) {
  const deadline = Date.now() + waitMs;
  let last = "";
  let stableSince = 0;
  while (Date.now() < deadline) {
    const state = await evaluate(call, attachmentStateExpression(), 5000);
    const grew = Number(state.attachmentCount || 0) > Number(beforeState.attachmentCount || 0);
    const ready = grew && !state.uploading && state.sendEnabled;
    const signature = JSON.stringify(state);
    if (ready && signature === last) {
      if (!stableSince) stableSince = Date.now();
      if (Date.now() - stableSince >= stableMs) return state;
    } else {
      last = signature;
      stableSince = 0;
    }
    await new Promise((resolve) => setTimeout(resolve, 1000));
  }
  throw new Error(`Timed out waiting for PDF attachment after ${waitMs}ms`);
}

async function attachLocalPdf(call, rawPath, options = {}) {
  const pdfPath = await resolveLocalPdfPath(rawPath);
  if (!pdfPath) return { attached: false };
  const before = await evaluate(call, attachmentStateExpression(), 5000);
  let nodeId = await queryFileInputNodeId(call);
  if (!nodeId) {
    const clicked = await clickAttachButton(call);
    if (!clicked?.ok) throw new Error(`Cannot open ChatGPT attach control: ${JSON.stringify(clicked)}`);
    await new Promise((resolve) => setTimeout(resolve, 1000));
    nodeId = await queryFileInputNodeId(call);
  }
  if (!nodeId) throw new Error("Cannot find ChatGPT file input after opening attach control");
  const setResult = await call("DOM.setFileInputFiles", { nodeId, files: [pdfPath] });
  if (setResult.error) throw new Error(`DOM.setFileInputFiles failed: ${JSON.stringify(setResult.error)}`);
  const ready = await waitForAttachmentReady(call, before, options.attachWaitMs, options.attachStableMs);
  return { attached: true, pdfPath, ready };
}

async function askChat(prompt, options = {}) {
  const { waitMs, minResponseChars, minWaitAfterFirstMs, stableMs } = normalizeAskWaitOptions(options);
  const attachOptions = normalizePdfAttachOptions(options);
  return withPage(async ({ call }) => {
    const before = await evaluate(call, readExpression());
    const beforeUserCount = before.turns.filter((turn) => turn.role === "user").length;
    const beforeAssistantCount = before.turns.filter((turn) => turn.role === "assistant").length;
    const promptJson = JSON.stringify(prompt);
    const attachment = attachOptions.pdfPath ? await attachLocalPdf(call, attachOptions.pdfPath, attachOptions) : { attached: false };

    const prepared = await evaluate(
      call,
      `(() => {
        const modal = document.querySelector("[data-testid='modal-conversation-history-rate-limit'], [id='modal-conversation-history-rate-limit']");
        if (modal) return { ok: false, reason: "modal", modalText: modal.innerText || "" };
        const box = document.querySelector("#prompt-textarea, textarea[data-testid='prompt-textarea'], div[contenteditable='true'][role='textbox']");
        if (!box) return { ok: false, reason: "no_prompt_box" };
        box.focus();
        if (box.tagName === "TEXTAREA") {
          box.value = "";
          box.dispatchEvent(new InputEvent("input", { bubbles: true, inputType: "deleteContentBackward" }));
        } else {
          box.innerHTML = "";
          box.dispatchEvent(new InputEvent("input", { bubbles: true, inputType: "deleteContentBackward" }));
        }
        return { ok: true };
      })()`,
    );
    if (!prepared?.ok) {
      throw new Error(`Cannot prepare ChatGPT prompt box: ${JSON.stringify(prepared)}`);
    }

    await call("Input.insertText", { text: prompt });
    await new Promise((resolve) => setTimeout(resolve, 700));

    const sent = await evaluate(
      call,
      `(() => {
        const buttons = Array.from(document.querySelectorAll("button"));
        const send = document.querySelector("button[data-testid='send-button']") ||
          buttons.find((button) => /send|发送/i.test(button.getAttribute("aria-label") || "")) ||
          buttons.find((button) => (button.innerText || "").trim() === "Send");
        if (!send) return { ok: false, reason: "no_send_button" };
        if (send.disabled || send.getAttribute("aria-disabled") === "true") {
          return { ok: false, reason: "send_disabled", html: send.outerHTML.slice(0, 300) };
        }
        send.click();
        return { ok: true };
      })()`,
    );
    if (!sent?.ok) {
      await call("Input.dispatchKeyEvent", {
        type: "keyDown",
        windowsVirtualKeyCode: 13,
        nativeVirtualKeyCode: 13,
        code: "Enter",
        key: "Enter",
      });
      await call("Input.dispatchKeyEvent", {
        type: "keyUp",
        windowsVirtualKeyCode: 13,
        nativeVirtualKeyCode: 13,
        code: "Enter",
        key: "Enter",
      });
    }

    const submitted = await waitForPromptSubmitted(call, beforeUserCount, sent);
    const after = await waitForStableAssistant(call, beforeAssistantCount, waitMs, {
      minResponseChars,
      minWaitAfterFirstMs,
      stableMs,
    });
    const response = [...after.turns].reverse().find((turn) => turn.role === "assistant")?.text || "";
    if (response.trim().length < minResponseChars) {
      throw new Error(
        `Assistant response remained shorter than minResponseChars ` +
          `(${response.trim().length} < ${minResponseChars})`,
      );
    }
    return {
      ok: true,
      promptChars: promptJson.length - 2,
      attachment,
      submitted,
      response,
      state: after,
    };
  }, options);
}

async function readRequestBody(request) {
  const chunks = [];
  for await (const chunk of request) chunks.push(chunk);
  const raw = Buffer.concat(chunks).toString("utf8");
  return raw ? JSON.parse(raw) : {};
}

async function serve(args) {
  rejectTargetOverride(args);
  const host = args.host || DEFAULT_HOST;
  const port = Number(args.port || DEFAULT_PORT);
  const cdp = args.cdp || DEFAULT_CDP;
  assertLoopbackUrl(cdp, "CDP endpoint");
  if (!LOOPBACK_HOSTS.has(host)) {
    throw new Error(`Refusing to bind non-loopback host for local profile service: ${host}`);
  }

  const server = http.createServer(async (request, response) => {
    try {
      if (request.method === "GET" && request.url === "/health") {
        const page = await findPage({ cdp });
        response.writeHead(200, { "content-type": "application/json" });
        response.end(JSON.stringify({ ok: true, cdp, page: { title: page.title, url: page.url } }));
        return;
      }
      if (request.method === "POST" && request.url === "/read") {
        await readRequestBody(request);
        const payload = await readChat({ cdp });
        response.writeHead(200, { "content-type": "application/json" });
        response.end(JSON.stringify(payload));
        return;
      }
      if (request.method === "POST" && request.url === "/ask") {
        const body = await readRequestBody(request);
        if (!body.prompt) throw new Error("POST /ask requires JSON field: prompt");
        const payload = await askChat(body.prompt, {
          cdp,
          waitMs: body.waitMs,
          minResponseChars: body.minResponseChars,
          minWaitAfterFirstMs: body.minWaitAfterFirstMs,
          stableMs: body.stableMs,
          pdfPath: body.pdfPath,
          attachWaitMs: body.attachWaitMs,
          attachStableMs: body.attachStableMs,
        });
        response.writeHead(200, { "content-type": "application/json" });
        response.end(JSON.stringify(payload));
        return;
      }
      response.writeHead(404, { "content-type": "application/json" });
      response.end(JSON.stringify({ ok: false, error: "not_found" }));
    } catch (error) {
      response.writeHead(500, { "content-type": "application/json" });
      response.end(JSON.stringify({ ok: false, error: String(error?.message || error) }));
    }
  });

  server.listen(port, host, () => {
    console.log(JSON.stringify({ ok: true, service: "nyxid-local-profile", host, port, cdp, conversationId: DEFAULT_CHAT_URL_FRAGMENT }));
  });
}

function rejectTargetOverride(args) {
  if (Object.hasOwn(args, "urlIncludes") || Object.hasOwn(args, "conversationId")) {
    throw new Error("Target conversation override is not supported by the local profile service");
  }
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const command = args._[0] || "read";
  if (command === "serve") {
    await serve(args);
    return;
  }
  if (command === "read") {
    rejectTargetOverride(args);
    console.log(JSON.stringify(await readChat(args), null, 2));
    return;
  }
  if (command === "ask") {
    rejectTargetOverride(args);
    const prompt = args.promptFile ? await readFile(args.promptFile, "utf8") : args.prompt;
    if (!prompt) throw new Error("ask requires --prompt or --promptFile");
    console.log(JSON.stringify(await askChat(prompt, args), null, 2));
    return;
  }
  throw new Error(`Unknown command: ${command}`);
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  main().catch((error) => {
    console.error(error);
    process.exit(1);
  });
}
