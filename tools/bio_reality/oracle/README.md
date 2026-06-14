# BioReality Oracle transport

BioReality oracle consultations are driven by `tools/bio_reality/oracle/oracle_client.py`.
The client accepts two transport forms:

- `nyxid://<service>[/path-prefix]` routes requests through `nyxid proxy request`.
- `http://127.0.0.1:8769` uses the legacy local bridge server.

The tracked `pipeline_config.json` leaves oracle integration disabled by default.
For a local daemon, enable it through environment variables so the account-specific
nyxid service name is not committed:

```bash
BIO_REALITY_ORACLE_ENABLED=1 \
BIO_REALITY_ORACLE_BIO_G_ENABLED=1 \
BIO_REALITY_ORACLE_BIO_PLAN_ENABLED=1 \
BIO_REALITY_ORACLE_SERVER_URL='nyxid://<service>[/path-prefix]' \
python3 tools/bio_reality/supervisor.py --interval-seconds 300 --max-dispatch 3
```

Do not pass `--plan-only` when the `bio-R` lane should execute Codex agent tasks.
That flag is a dry-run mode: it plans agent tasks and records `planned_only`
dispatch results without invoking `codex exec`.

## Health check

```bash
python3 tools/bio_reality/oracle/oracle_client.py \
  --server-url 'nyxid://<service>[/path-prefix]' \
  --health-check
```

If this reports `nyxid_login_required`, refresh the local nyxid session with
`nyxid login`.

## Send a query

```bash
python3 tools/bio_reality/oracle/oracle_client.py \
  --server-url 'nyxid://<service>[/path-prefix]' \
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
The nyxid transport does not use that userscript.
