# LeWM Cross-Env Replication

| env | episodes | transitions | learned AUROC [CI] | matched [CI] | UER before -> after | claim |
|---|---:|---:|---:|---:|---:|---|
| pusht | 150 | 3092 | 1.0000 [1.0000, 1.0000] | 0.3094 [0.2995, 0.3183] | 0.1846 [0.1675, 0.2020] -> 0.0000 [0.0000, 0.0000] | positive |
| reacher | 150 | 6000 | 0.6619 [0.6195, 0.7006] | 0.5497 [0.4982, 0.5974] | 0.2650 [0.2237, 0.3100] -> 0.2300 [0.2033, 0.2583] | negative_or_inconclusive |
| cube | 150 | 6000 | 0.6102 [0.5677, 0.6520] | 0.5072 [0.4584, 0.5538] | 0.2483 [0.2196, 0.2767] -> 0.2100 [0.1833, 0.2325] | negative_or_inconclusive |
