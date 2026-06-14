# LeWM reacher Cross-Env Gap Ledger

- status: evaluated
- claim: negative_or_inconclusive
- episodes: 150; transitions: 6000
- tau: 0.00770142

| arm | AUROC [CI] | UER [CI] |
|---|---:|---:|
| learned_logistic_emb | 0.6619 [0.6195, 0.7006] | 0.2300 [0.2033, 0.2583] |
| matched_random_logistic_emb | 0.5497 [0.4982, 0.5974] | 0.2650 [0.2237, 0.3100] |
| vanilla | 0.5000 [0.5000, 0.5000] | 0.2650 [0.2237, 0.3100] |
