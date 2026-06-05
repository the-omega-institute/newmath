import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentialClosureCarrier [AskSetup] [PackageSetup]
    (T M S Q L U W R A H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  UnaryHistory T ∧ UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory Q ∧
    UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory W ∧ UnaryHistory R ∧
      UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg

theorem SequentialClosureSequenceLimitHandoff [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N limitRead windowRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg ->
      Cont L U limitRead ->
        Cont limitRead W windowRead ->
          Cont windowRead A sealRead ->
            Cont sealRead N named ->
              PkgSig bundle named pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row named ∧ UnaryHistory row ∧
                    PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
                      hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
                        hsame row A ∨ hsame row named)
                  (fun row : BHist =>
                    hsame row named ∧ Cont L U limitRead ∧
                      Cont limitRead W windowRead ∧ Cont windowRead A sealRead ∧
                        PkgSig bundle P pkg)
                  hsame ∧ UnaryHistory limitRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier limitRoute windowRoute sealRoute namedRoute namedPkg
  obtain ⟨_topologyUnary, _metricUnary, _subsetUnary, _sourceUnary, limitUnaryBase,
    ledgerUnary, windowUnaryBase, _regSeqUnary, sealUnaryBase, _transportUnary,
    _continuationUnary, pUnary, nUnary, pPkg⟩ := carrier
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnaryBase ledgerUnary limitRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed limitUnary windowUnaryBase windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary sealUnaryBase sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row named ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨ hsame row L ∨
            hsame row U ∨ hsame row W ∨ hsame row R ∨ hsame row A ∨
              hsame row named)
        (fun row : BHist =>
          hsame row named ∧ Cont L U limitRead ∧ Cont limitRead W windowRead ∧
            Cont windowRead A sealRead ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro named
        ⟨hsame_refl named, namedUnary, namedPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, limitRoute, windowRoute, sealRoute, pPkg⟩
  }
  exact ⟨cert, limitUnary, windowUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp
