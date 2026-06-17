#!/usr/bin/env node

import assert from "node:assert/strict";
import {
  assertLoopbackUrl,
  isAuthorizedChatUrl,
  normalizeAskWaitOptions,
  selectAuthorizedPage,
  waitForStableAssistant,
} from "./nyxid_local_profile_service.mjs";

const fragment = "6a32835f-e560-83ee-a061-8fe3b0ddfbb9";
const authorized = {
  type: "page",
  url: `https://chatgpt.com/g/g-p-69f66d6480a8819183ee88a54e5b8f3c/c/${fragment}`,
  title: "BEDC - branch",
  webSocketDebuggerUrl: "ws://127.0.0.1:9222/devtools/page/auth",
};

const genericChat = {
  type: "page",
  url: "https://chatgpt.com/",
  title: "ChatGPT",
  webSocketDebuggerUrl: "ws://127.0.0.1:9222/devtools/page/generic",
};

const otherPage = {
  type: "page",
  url: `https://example.com/c/${fragment}`,
  title: "Example",
  webSocketDebuggerUrl: "ws://127.0.0.1:9222/devtools/page/example",
};

const poolPage = {
  type: "page",
  url: `http://127.0.0.1:8765/pool/${fragment}`,
  title: "Local pool",
  webSocketDebuggerUrl: "ws://127.0.0.1:9222/devtools/page/pool",
};

assert.equal(
  selectAuthorizedPage([genericChat, authorized], { conversationId: fragment }).webSocketDebuggerUrl,
  authorized.webSocketDebuggerUrl,
);

assert.equal(
  selectAuthorizedPage([otherPage, poolPage, authorized], { conversationId: fragment }).webSocketDebuggerUrl,
  authorized.webSocketDebuggerUrl,
);

assert.equal(selectAuthorizedPage([authorized], {}).webSocketDebuggerUrl, authorized.webSocketDebuggerUrl);
assert.equal(isAuthorizedChatUrl(authorized.url, fragment), true);
assert.equal(isAuthorizedChatUrl(otherPage.url, fragment), false);
assert.equal(isAuthorizedChatUrl(poolPage.url, fragment), false);
assert.equal(isAuthorizedChatUrl("https://chatgpt.com/not-c/" + fragment, fragment), false);
assert.equal(isAuthorizedChatUrl("https://chatgpt.com/not-c/" + fragment + "/c", fragment), false);
assert.equal(isAuthorizedChatUrl("https://chatgpt.com/" + fragment, fragment), false);

assert.throws(
  () => selectAuthorizedPage([genericChat], { conversationId: fragment }),
  /Authorized ChatGPT conversation not found/,
);

assert.throws(
  () => selectAuthorizedPage([otherPage], { conversationId: fragment }),
  /Authorized ChatGPT conversation not found/,
);

assert.throws(
  () => selectAuthorizedPage([{ ...authorized, webSocketDebuggerUrl: "" }], { conversationId: fragment }),
  /no CDP websocket/,
);

assert.throws(
  () => selectAuthorizedPage([{ ...authorized, webSocketDebuggerUrl: "ws://192.0.2.1:9222/devtools/page/auth" }]),
  /Refusing non-loopback CDP websocket/,
);

assert.throws(
  () => selectAuthorizedPage([authorized], { conversationId: "" }),
  /fragment is required/,
);

assert.throws(
  () => selectAuthorizedPage([authorized], { conversationId: "true" }),
  /fragment is required/,
);

assert.doesNotThrow(() => assertLoopbackUrl("http://127.0.0.1:9222", "CDP endpoint"));
assert.doesNotThrow(() => assertLoopbackUrl("http://localhost:9222", "CDP endpoint"));
assert.throws(
  () => assertLoopbackUrl("http://192.0.2.1:9222", "CDP endpoint"),
  /Refusing non-loopback CDP endpoint/,
);

{
  const calls = [];
  const shortAssistantState = {
    turns: [
      { role: "user", text: "question" },
      { role: "assistant", text: "I" },
    ],
  };
  async function fakeCall(method, params) {
    calls.push({ method, params });
    const expression = params.expression || "";
    if (expression.includes("stop-button")) {
      return { result: { result: { value: false } } };
    }
    return { result: { result: { value: shortAssistantState } } };
  }

  await assert.rejects(
    waitForStableAssistant(fakeCall, 0, 1200, {
      minResponseChars: 80,
      minWaitAfterFirstMs: 30000,
      stableMs: 100,
    }),
    /Timed out waiting for assistant response/,
  );
  assert.ok(calls.length > 0);
}

assert.deepEqual(normalizeAskWaitOptions({
  waitMs: 1200,
  minResponseChars: 1,
  minWaitAfterFirstMs: 1,
  stableMs: 1,
}), {
  waitMs: 1200,
  minResponseChars: 80,
  minWaitAfterFirstMs: 15000,
  stableMs: 5000,
});

console.log("nyxid_local_profile_service single-chat tests passed");
