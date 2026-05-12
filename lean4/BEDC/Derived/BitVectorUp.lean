import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def BitVectorSourceClassifier
    (length spine ledger provenance length' spine' ledger' provenance' : BHist) : Prop :=
  hsame length length' ∧ hsame spine spine' ∧ hsame ledger ledger' ∧
    hsame provenance provenance'

theorem BitVectorSourceClassifier_laws :
    (∀ {n s l p : BHist}, Cont n s l → hsame p p →
      BitVectorSourceClassifier n s l p n s l p) ∧
      (∀ {n s l p n' s' l' p' : BHist},
        BitVectorSourceClassifier n s l p n' s' l' p' →
          BitVectorSourceClassifier n' s' l' p' n s l p) ∧
        (∀ {n s l p n' s' l' p' n'' s'' l'' p'' : BHist},
          BitVectorSourceClassifier n s l p n' s' l' p' →
            BitVectorSourceClassifier n' s' l' p' n'' s'' l'' p'' →
              BitVectorSourceClassifier n s l p n'' s'' l'' p'') := by
  constructor
  · intro n s l p _route sameProvenance
    constructor
    · exact hsame_refl n
    · constructor
      · exact hsame_refl s
      · constructor
        · exact hsame_refl l
        · exact sameProvenance
  · constructor
    · intro n s l p n' s' l' p' classified
      cases classified with
      | intro sameLength rest =>
          cases rest with
          | intro sameSpine rest =>
              cases rest with
              | intro sameLedger sameProvenance =>
                  constructor
                  · exact hsame_symm sameLength
                  · constructor
                    · exact hsame_symm sameSpine
                    · constructor
                      · exact hsame_symm sameLedger
                      · exact hsame_symm sameProvenance
    · intro n s l p n' s' l' p' n'' s'' l'' p'' left right
      cases left with
      | intro sameLengthLeft leftRest =>
          cases leftRest with
          | intro sameSpineLeft leftRest =>
              cases leftRest with
              | intro sameLedgerLeft sameProvenanceLeft =>
                  cases right with
                  | intro sameLengthRight rightRest =>
                      cases rightRest with
                      | intro sameSpineRight rightRest =>
                          cases rightRest with
                          | intro sameLedgerRight sameProvenanceRight =>
                              constructor
                              · exact hsame_trans sameLengthLeft sameLengthRight
                              · constructor
                                · exact hsame_trans sameSpineLeft sameSpineRight
                                · constructor
                                  · exact hsame_trans sameLedgerLeft sameLedgerRight
                                  · exact hsame_trans sameProvenanceLeft sameProvenanceRight

end BEDC.Derived.BitVectorUp
