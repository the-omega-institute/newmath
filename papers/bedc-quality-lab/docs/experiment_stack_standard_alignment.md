# Experiment Stack Standard Alignment

This document is a pointer-only alignment map. The canonical card contract is `reports/canonical/experiment_stack_cards.json:$.cards`.

| external standard | external pointer | local card pointers |
| --- | --- | --- |
| NeurIPS checklist | `https://neurips.cc/public/guides/PaperChecklist` | `reports/canonical/experiment_stack_cards.json:$.cards[0]`, `reports/canonical/experiment_stack_cards.json:$.cards[2]`, `reports/canonical/experiment_stack_cards.json:$.cards[8]`, `reports/canonical/experiment_stack_cards.json:$.cards[12]` |
| Papers with Code code completeness | `https://paperswithcode.com/about` | `reports/canonical/experiment_stack_cards.json:$.cards[10]`, `reports/canonical/experiment_stack_cards.json:$.cards[7]` |
| ACM artifact badging | `https://www.acm.org/publications/policies/artifact-review-badging` | `reports/canonical/experiment_stack_cards.json:$.cards[10]`, `reports/canonical/experiment_stack_cards.json:$.cards[13]` |
| Model Cards | `https://modelcards.withgoogle.com/about` | `reports/canonical/experiment_stack_cards.json:$.cards[11]`, `reports/canonical/experiment_stack_cards.json:$.cards[12]` |
| NIST AI RMF | `https://www.nist.gov/itl/ai-risk-management-framework` | `reports/canonical/experiment_stack_cards.json:$.cards[12]`, `reports/canonical/experiment_stack_cards.json:$.cards[13]` |

Local gate status is read from `reports/canonical/experiment_stack_cards.json:$.cards[*].hardgates`. External standards remain cited by URL only; this file does not copy checklist, badge, or framework prose.
