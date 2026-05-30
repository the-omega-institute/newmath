# BioReality Oracle bridge

Independent ChatGPT bridge for the BioReality pipeline, distinct from
the BEDC oracle. Same architecture as BEDC, fork-namespaced so the two
oracles run side by side without collision.

## Components

- bio_reality_oracle_server.py: local HTTP server on :8769
- bio_reality_oracle_macos.user.js: Tampermonkey userscript for
  ChatGPT.com tabs (Chrome / Firefox / Safari with Tampermonkey)
- oracle_client.py: stdlib Python HTTP client the daemon uses

## Installation

1. Open Chrome (the user account you reserved for BioReality)
2. Tampermonkey -> Create a new script
3. Paste contents of bio_reality_oracle_macos.user.js
4. Save
5. Navigate to https://chatgpt.com/g/g-p-.../哥本哈根之路/project (or any
   chatgpt.com URL)
6. The BioReality oracle panel appears top-right with [bio] prefix
7. Click ACTIVATE on each tab you want to use as a worker

## Start the local server

```bash
python3 tools/bio_reality/oracle/bio_reality_oracle_server.py
```

## Health check

```bash
python3 tools/bio_reality/oracle/oracle_client.py --health-check
```

## Send a query

```bash
python3 tools/bio_reality/oracle/oracle_client.py --query "..." --intended-claim h0.M.equals.WNR.CUN
```

## Parallel tabs

Open multiple chatgpt.com tabs, ACTIVATE each via panel. Server
dispatches one task per active tab in round-robin.
