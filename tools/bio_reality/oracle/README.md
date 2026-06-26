# BioReality Oracle transport

BioReality oracle consultations are driven by `tools/bio_reality/oracle/oracle_client.py`.
The client accepts two transport forms:

- `nyxid-oracle://<pool-slug>` routes requests through the NyxID oracle relay
  (`nyxid oracle ask/result/status`).
- `nyxid://<service>[/path-prefix]` keeps compatibility with direct
  `nyxid proxy request` relays.
- `http://127.0.0.1:8769` uses the legacy local bridge server.

The tracked `pipeline_config.json` leaves oracle integration disabled by default.
For a local daemon, enable it through environment variables so the account-specific
nyxid service name is not committed:

```bash
BIO_REALITY_ORACLE_ENABLED=1 \
BIO_REALITY_ORACLE_BIO_G_ENABLED=1 \
BIO_REALITY_ORACLE_BIO_PLAN_ENABLED=1 \
BIO_REALITY_ORACLE_POOL='omega-oracle' \
BIO_REALITY_ORACLE_CONVERSATION_ID='conv_a21ca96c74f74ad2' \
python3 tools/bio_reality/supervisor.py --interval-seconds 300 --max-dispatch 3
```

When `BIO_REALITY_ORACLE_CONVERSATION_ID` is set, `bio-G` and `bio-Plan` keep
using that NyxID bridge conversation instead of lane-topic conversation records.

Do not pass `--plan-only` when the `bio-R` lane should execute Codex agent tasks.
That flag is a dry-run mode: it plans agent tasks and records `planned_only`
dispatch results without invoking `codex exec`.

## Health check

```bash
python3 tools/bio_reality/oracle/oracle_client.py \
  --server-url 'nyxid-oracle://omega-oracle' \
  --health-check
```

If this reports `nyxid_login_required`, refresh the local nyxid session with
`nyxid login`.

## Send a query

```bash
python3 tools/bio_reality/oracle/oracle_client.py \
  --server-url 'nyxid-oracle://omega-oracle' \
  --query "..." \
  --intended-claim h0.M.equals.WNR.CUN
```

## Legacy local bridge

The old local HTTP bridge remains available for compatibility:

```bash
python3 tools/bio_reality/oracle/bio_reality_oracle_server.py
python3 tools/bio_reality/oracle/oracle_client.py --health-check
```

That bridge depends on `bio_reality_oracle_macos.user.js` in an active ChatGPT tab.
The NyxID oracle relay transport does not use the BioReality userscript; worker
capacity is managed by NyxID oracle browser workers attached to the selected pool.
