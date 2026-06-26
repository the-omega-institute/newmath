# PushT Independent Export Round3-C

- status: `ok`
- conclusion: **single-export artifact bounded**
- split seed: `1701`; bootstrap: `314159` / `500` eval-episode resamples
- not_claimed: No OOD arm is claimed; this tests independent clean PushT episode populations only.

## Population Overlap

| export | selected_ep_idx min..max | overlap with original | valid transitions | identity max delta |
|---|---:|---:|---:|---:|
| C3a_from_1200_first150_valid | 1200..1349 | 0 | 3698 | 1.19212167e-07 |
| C3b_stratified_random_seed2718 | 7..2039 | 0 | 3374 | 2.33136457e-08 |

## h=1 / h=5 Table

| export | method | h1 AUROC | h1 UER | h5 AUROC | h10 AUROC | confirmed rule |
|---|---|---:|---:|---:|---:|---:|
| C3a_from_1200_first150_valid | posthoc | 0.9990 [0.9979, 0.9997] | 0.0129 [0.0075, 0.0190] | 1.0000 [1.0000, 1.0000] | 0.9944 [0.9941, 0.9956] | true |
| C3a_from_1200_first150_valid | native | 1.0000 [1.0000, 1.0000] | 0.0000 [0.0000, 0.0000] | 1.0000 [1.0000, 1.0000] | 1.0000 [1.0000, 1.0000] | true |
| C3b_stratified_random_seed2718 | posthoc | 0.7444 [0.6668, 0.8151] | 0.1525 [0.1196, 0.1849] | 0.8536 [0.7439, 0.9395] | 0.8299 [0.7537, 0.8982] | false |
| C3b_stratified_random_seed2718 | native | 0.8001 [0.7396, 0.8633] | 0.1186 [0.0913, 0.1534] | 0.8614 [0.7481, 0.9488] | 0.8626 [0.7690, 0.9305] | false |

## Anchor Labels

| export | label h1 max delta | train/eval anchors | eval h1 base rate | eval h5 base rate |
|---|---:|---:|---:|---:|
| C3a_from_1200_first150_valid | 2.17628364e-07 | 2054 / 698 | 0.2249 | 0.2509 |
| C3b_stratified_random_seed2718 | 2.88968091e-08 | 1765 / 649 | 0.2419 | 0.2136 |

