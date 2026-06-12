# Gaussian-OU multi-seed quality experiment

- Generated at: `2026-06-01T06:42:35.518655+00:00`
- Seed base: `430`
- Seed count: `20`
- Seeds: `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958`
- Rho grid: `0.3, 0.6, 0.82, 0.95`
- Sample count: `384`
- Arms: `fallback, torch`

## Metric error bars

### rho=0.3

| arm | metric | mean ± std | 95% CI half-width | n |
| --- | --- | ---: | ---: | ---: |
| fallback | `linear_identifiability_r2` | 0.924277 ± 0.008234 | 0.003609 | 20 |
| fallback | `approx_identifiability_proxy` | 0.850474 ± 0.029314 | 0.012847 | 20 |
| fallback | `orthogonality_error` | 0.196623 ± 0.073759 | 0.032326 | 20 |
| fallback | `covariance_deviation` | 0.197179 ± 0.073930 | 0.032401 | 20 |
| fallback | `quality_benefit` | 0.887375 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_cost` | 0.030000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_debt` | 0.900000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_q` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_margin` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| torch | `linear_identifiability_r2` | 0.233143 ± 0.120578 | 0.052846 | 20 |
| torch | `approx_identifiability_proxy` | 0.022259 ± 0.049096 | 0.021517 | 20 |
| torch | `orthogonality_error` | 0.563970 ± 0.381589 | 0.167239 | 20 |
| torch | `covariance_deviation` | 1.411310 ± 0.011017 | 0.004828 | 20 |
| torch | `quality_benefit` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_cost` | 0.060000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_debt` | 1.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_q` | -1.060000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_margin` | -1.060000 ± 0.000000 | 0.000000 | 20 |

### rho=0.6

| arm | metric | mean ± std | 95% CI half-width | n |
| --- | --- | ---: | ---: | ---: |
| fallback | `linear_identifiability_r2` | 0.924277 ± 0.008234 | 0.003609 | 20 |
| fallback | `approx_identifiability_proxy` | 0.850474 ± 0.029314 | 0.012847 | 20 |
| fallback | `orthogonality_error` | 0.196623 ± 0.073759 | 0.032326 | 20 |
| fallback | `covariance_deviation` | 0.197179 ± 0.073930 | 0.032401 | 20 |
| fallback | `quality_benefit` | 0.887375 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_cost` | 0.030000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_debt` | 0.900000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_q` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_margin` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| torch | `linear_identifiability_r2` | 0.695167 ± 0.197264 | 0.086455 | 20 |
| torch | `approx_identifiability_proxy` | 0.528975 ± 0.197941 | 0.086751 | 20 |
| torch | `orthogonality_error` | 0.196834 ± 0.154526 | 0.067724 | 20 |
| torch | `covariance_deviation` | 0.935867 ± 0.105937 | 0.046429 | 20 |
| torch | `quality_benefit` | 0.206061 ± 0.366215 | 0.160501 | 20 |
| torch | `quality_cost` | 0.060000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_debt` | 1.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_q` | -0.853939 ± 0.366215 | 0.160501 | 20 |
| torch | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_margin` | -0.853939 ± 0.366215 | 0.160501 | 20 |

### rho=0.82

| arm | metric | mean ± std | 95% CI half-width | n |
| --- | --- | ---: | ---: | ---: |
| fallback | `linear_identifiability_r2` | 0.924277 ± 0.008234 | 0.003609 | 20 |
| fallback | `approx_identifiability_proxy` | 0.850474 ± 0.029314 | 0.012847 | 20 |
| fallback | `orthogonality_error` | 0.196623 ± 0.073759 | 0.032326 | 20 |
| fallback | `covariance_deviation` | 0.197179 ± 0.073930 | 0.032401 | 20 |
| fallback | `quality_benefit` | 0.887375 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_cost` | 0.030000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_debt` | 0.900000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_q` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_margin` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| torch | `linear_identifiability_r2` | 0.894982 ± 0.104078 | 0.045614 | 20 |
| torch | `approx_identifiability_proxy` | 0.824738 ± 0.105693 | 0.046322 | 20 |
| torch | `orthogonality_error` | 0.041199 ± 0.039785 | 0.017437 | 20 |
| torch | `covariance_deviation` | 0.479554 ± 0.045376 | 0.019887 | 20 |
| torch | `quality_benefit` | 0.761337 ± 0.329785 | 0.144535 | 20 |
| torch | `quality_cost` | 0.060000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_debt` | 1.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_q` | -0.298663 ± 0.329785 | 0.144535 | 20 |
| torch | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_margin` | -0.298663 ± 0.329785 | 0.144535 | 20 |

### rho=0.95

| arm | metric | mean ± std | 95% CI half-width | n |
| --- | --- | ---: | ---: | ---: |
| fallback | `linear_identifiability_r2` | 0.924277 ± 0.008234 | 0.003609 | 20 |
| fallback | `approx_identifiability_proxy` | 0.850474 ± 0.029314 | 0.012847 | 20 |
| fallback | `orthogonality_error` | 0.196623 ± 0.073759 | 0.032326 | 20 |
| fallback | `covariance_deviation` | 0.197179 ± 0.073930 | 0.032401 | 20 |
| fallback | `quality_benefit` | 0.887375 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_cost` | 0.030000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_debt` | 0.900000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_q` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| fallback | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| fallback | `quality_margin` | -0.042625 ± 0.016492 | 0.007228 | 20 |
| torch | `linear_identifiability_r2` | 0.943961 ± 0.019357 | 0.008483 | 20 |
| torch | `approx_identifiability_proxy` | 0.922940 ± 0.019154 | 0.008394 | 20 |
| torch | `orthogonality_error` | 0.011797 ± 0.009419 | 0.004128 | 20 |
| torch | `covariance_deviation` | 0.144576 ± 0.015358 | 0.006731 | 20 |
| torch | `quality_benefit` | 0.933451 ± 0.019167 | 0.008400 | 20 |
| torch | `quality_cost` | 0.060000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_debt` | 1.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_q` | -0.126549 ± 0.019167 | 0.008400 | 20 |
| torch | `quality_threshold` | 0.000000 ± 0.000000 | 0.000000 | 20 |
| torch | `quality_margin` | -0.126549 ± 0.019167 | 0.008400 | 20 |

## Encoder contrast

| rho | metric | fallback mean ± std | torch mean ± std | torch status |
| --- | --- | ---: | ---: | --- |
| 0.3 | `linear_identifiability_r2` | 0.924277 ± 0.008234 (95% CI ± 0.003609; n=20) | 0.233143 ± 0.120578 (95% CI ± 0.052846; n=20) | ok |
| 0.3 | `approx_identifiability_proxy` | 0.850474 ± 0.029314 (95% CI ± 0.012847; n=20) | 0.022259 ± 0.049096 (95% CI ± 0.021517; n=20) | ok |
| 0.3 | `orthogonality_error` | 0.196623 ± 0.073759 (95% CI ± 0.032326; n=20) | 0.563970 ± 0.381589 (95% CI ± 0.167239; n=20) | ok |
| 0.3 | `covariance_deviation` | 0.197179 ± 0.073930 (95% CI ± 0.032401; n=20) | 1.411310 ± 0.011017 (95% CI ± 0.004828; n=20) | ok |
| 0.3 | `quality_q` | -0.042625 ± 0.016492 (95% CI ± 0.007228; n=20) | -1.060000 ± 0.000000 (95% CI ± 0.000000; n=20) | ok |
| 0.3 | `quality_debt` | 0.900000 ± 0.000000 (95% CI ± 0.000000; n=20) | 1.000000 ± 0.000000 (95% CI ± 0.000000; n=20) | ok |
| 0.6 | `linear_identifiability_r2` | 0.924277 ± 0.008234 (95% CI ± 0.003609; n=20) | 0.695167 ± 0.197264 (95% CI ± 0.086455; n=20) | ok |
| 0.6 | `approx_identifiability_proxy` | 0.850474 ± 0.029314 (95% CI ± 0.012847; n=20) | 0.528975 ± 0.197941 (95% CI ± 0.086751; n=20) | ok |
| 0.6 | `orthogonality_error` | 0.196623 ± 0.073759 (95% CI ± 0.032326; n=20) | 0.196834 ± 0.154526 (95% CI ± 0.067724; n=20) | ok |
| 0.6 | `covariance_deviation` | 0.197179 ± 0.073930 (95% CI ± 0.032401; n=20) | 0.935867 ± 0.105937 (95% CI ± 0.046429; n=20) | ok |
| 0.6 | `quality_q` | -0.042625 ± 0.016492 (95% CI ± 0.007228; n=20) | -0.853939 ± 0.366215 (95% CI ± 0.160501; n=20) | ok |
| 0.6 | `quality_debt` | 0.900000 ± 0.000000 (95% CI ± 0.000000; n=20) | 1.000000 ± 0.000000 (95% CI ± 0.000000; n=20) | ok |
| 0.82 | `linear_identifiability_r2` | 0.924277 ± 0.008234 (95% CI ± 0.003609; n=20) | 0.894982 ± 0.104078 (95% CI ± 0.045614; n=20) | ok |
| 0.82 | `approx_identifiability_proxy` | 0.850474 ± 0.029314 (95% CI ± 0.012847; n=20) | 0.824738 ± 0.105693 (95% CI ± 0.046322; n=20) | ok |
| 0.82 | `orthogonality_error` | 0.196623 ± 0.073759 (95% CI ± 0.032326; n=20) | 0.041199 ± 0.039785 (95% CI ± 0.017437; n=20) | ok |
| 0.82 | `covariance_deviation` | 0.197179 ± 0.073930 (95% CI ± 0.032401; n=20) | 0.479554 ± 0.045376 (95% CI ± 0.019887; n=20) | ok |
| 0.82 | `quality_q` | -0.042625 ± 0.016492 (95% CI ± 0.007228; n=20) | -0.298663 ± 0.329785 (95% CI ± 0.144535; n=20) | ok |
| 0.82 | `quality_debt` | 0.900000 ± 0.000000 (95% CI ± 0.000000; n=20) | 1.000000 ± 0.000000 (95% CI ± 0.000000; n=20) | ok |
| 0.95 | `linear_identifiability_r2` | 0.924277 ± 0.008234 (95% CI ± 0.003609; n=20) | 0.943961 ± 0.019357 (95% CI ± 0.008483; n=20) | ok |
| 0.95 | `approx_identifiability_proxy` | 0.850474 ± 0.029314 (95% CI ± 0.012847; n=20) | 0.922940 ± 0.019154 (95% CI ± 0.008394; n=20) | ok |
| 0.95 | `orthogonality_error` | 0.196623 ± 0.073759 (95% CI ± 0.032326; n=20) | 0.011797 ± 0.009419 (95% CI ± 0.004128; n=20) | ok |
| 0.95 | `covariance_deviation` | 0.197179 ± 0.073930 (95% CI ± 0.032401; n=20) | 0.144576 ± 0.015358 (95% CI ± 0.006731; n=20) | ok |
| 0.95 | `quality_q` | -0.042625 ± 0.016492 (95% CI ± 0.007228; n=20) | -0.126549 ± 0.019167 (95% CI ± 0.008400; n=20) | ok |
| 0.95 | `quality_debt` | 0.900000 ± 0.000000 (95% CI ± 0.000000; n=20) | 1.000000 ± 0.000000 (95% CI ± 0.000000; n=20) | ok |

## Seed distribution

| rho | arm | status | seeds |
| --- | --- | --- | --- |
| 0.3 | fallback | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
| 0.3 | torch | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
| 0.6 | fallback | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
| 0.6 | torch | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
| 0.82 | fallback | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
| 0.82 | torch | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
| 0.95 | fallback | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
| 0.95 | torch | ok | `430, 1476, 2596, 3790, 5058, 6400, 7816, 9306, 10870, 12508, 14220, 16006, 17866, 19800, 21808, 23890, 26046, 28276, 30580, 32958` |
