# Compute-Value Episode Decomposition

- episodes: `55`
- anchors: `634`
- policy mean episode delta: `0.00137344165`
- scalar RankNet mean episode delta: `0.00697758231`
- oracle mean episode delta: `-0.0127955655`
- missed oracle top5 share: `0.416210581`

| scorer | mean | median | positive episodes | negative episodes |
|---|---:|---:|---:|---:|
| `policy` | 0.00137344165 | 0.000265671627 | 28 | 27 |
| `scalar_ranknet` | 0.00697758231 | 0.00526312809 | 36 | 19 |
| `oracle` | -0.0127955655 | -0.00833690337 | 12 | 43 |
| `random_reference` | 0.024508714 | 0.0197892229 | 45 | 10 |

Worst missed-oracle episodes:

- episode `115`: missed `0.110269308` over `14` anchors
- episode `277`: missed `0.0685337253` over `10` anchors
- episode `81`: missed `0.0538383465` over `14` anchors
- episode `193`: missed `0.0522963772` over `6` anchors
- episode `145`: missed `0.0442403398` over `11` anchors
- episode `39`: missed `0.0419313406` over `10` anchors
- episode `24`: missed `0.0413007215` over `8` anchors
- episode `223`: missed `0.0263848781` over `14` anchors
