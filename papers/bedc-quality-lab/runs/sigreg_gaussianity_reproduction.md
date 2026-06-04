# SIGReg Gaussianity Reproduction Sidecar

- artifact: `runs/sigreg_gaussianity_reproduction.json`
- schema_id: `bedc-quality-lab:sigreg-gaussianity-reproduction-sidecar`
- canonical_role: `sidecar_not_in_CANONICAL_REPORTS`
- verdict: `positive_control_passed_pointer_only`
- promotion: `none`

## Hardgates

- HG-F1: `pass`
- HG-F2: `pass`
- HG-F3: `pass`
- HG-F4: `pass`
- HG-F5: `pass`

## Paired CI Cells

- laplace: SIGReg mean=0.01274670, CI95=[0.01195232, 0.01360312], proxy mean=-0.00220993, proxy CI95=[-0.01128287, 0.00613809], HG-F1=pass
- uniform: SIGReg mean=0.01290453, CI95=[0.01235691, 0.01349673], proxy mean=-0.00429606, proxy CI95=[-0.01339195, 0.00403070], HG-F1=pass
- student_t_df3: SIGReg mean=0.03335277, CI95=[0.02387523, 0.04786720], proxy mean=-0.00344313, proxy CI95=[-0.00884692, 0.00237202], HG-F1=pass
- generalized_normal_alpha4: SIGReg mean=0.00436481, CI95=[0.00417071, 0.00457991], proxy mean=0.00557021, proxy CI95=[-0.00152269, 0.01311395], HG-F1=pass

## Proxy Contrast

- laplace: sigreg_separates=True, proxy_separates=False, status=disagreement_preserved
- uniform: sigreg_separates=True, proxy_separates=False, status=disagreement_preserved
- student_t_df3: sigreg_separates=True, proxy_separates=False, status=disagreement_preserved
- generalized_normal_alpha4: sigreg_separates=True, proxy_separates=False, status=disagreement_preserved

## Not Claimed

- SIGReg statistic reproduction is not a complete LeJEPA claim
- no global or universal Gaussianity certification
- no project-wide quality conclusion
- no tensor NameCert conclusion
- no language-model behavior conclusion
- no solved model-quality conclusion
- no claim outside the listed source families, seeds, directions, and frequency grid

## Revoke Conditions

- revoke if fresh paired seeds remove Gaussian versus non-Gaussian CI separation
- revoke if a larger sample or a different direction and frequency grid removes CI separation
- revoke if any collapse or isometry guard fails
- revoke if the statistic computation path reads ground-truth labels or source-family keys
