import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteDimensionalNormEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteDimensionalNormEquivalenceCarrier [AskSetup] [PackageSetup]
    (V K A B R L U H T P N coordinateRead lowerRead upperRead comparisonRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory V ∧ UnaryHistory K ∧ UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory R ∧
    UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont V K coordinateRead ∧ Cont A R lowerRead ∧
        Cont B R upperRead ∧ Cont L U comparisonRead ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem FiniteDimensionalNormEquivalenceNameCertObligations [AskSetup] [PackageSetup]
    {V K A B R L U H T P N coordinateRead lowerRead upperRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteDimensionalNormEquivalenceCarrier V K A B R L U H T P N coordinateRead lowerRead
        upperRead comparisonRead bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row V ∨ hsame row K ∨ hsame row A ∨ hsame row B ∨ hsame row R ∨
              hsame row L ∨ hsame row U ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row N ∨ hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V K coordinateRead ∧ Cont A R lowerRead ∧
              Cont B R upperRead ∧ Cont L U comparisonRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_unaryV, _unaryK, _unaryA, _unaryB, _unaryR, _unaryL, _unaryU,
    _unaryH, _unaryT, _unaryP, unaryN, coordinateRoute, lowerRoute, upperRoute,
    comparisonRoute, provenancePkg, namePkg⟩ := carrier
  have sourceName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row ∧ PkgSig bundle row pkg) N := by
    exact ⟨hsame_refl N, unaryN, namePkg⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceName
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
        intro _row _other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inl source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right.left, coordinateRoute, lowerRoute, upperRoute, comparisonRoute,
          provenancePkg, namePkg⟩
  }

end BEDC.Derived.FiniteDimensionalNormEquivalenceUp
