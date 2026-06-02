import BEDC.Derived.DedekindMacNeilleCompletionUp.CutClosure
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DedekindMacNeilleCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DedekindMacNeilleCompletionNameCert_obligations [AskSetup] [PackageSetup]
    {L U K Q E H C P N lowerUpper realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L U K ->
      Cont K Q E ->
        Cont E C realSeal ->
          UnaryHistory L ->
            UnaryHistory U ->
              UnaryHistory Q ->
                UnaryHistory C ->
                  PkgSig bundle realSeal pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row N ∧
                          List.Mem
                            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist K)
                            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow
                              (DedekindMacNeilleCompletionUp.mk L U K Q E H C P N)))
                      (fun row : BHist => hsame row N)
                      (fun row : BHist => hsame row N)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeLU routeKQ routeEC unaryL unaryU unaryQ unaryC realPkg
  have closure :=
    DedekindMacNeilleCompletionCarrier_cut_closure
      (L := L) (U := U) (K := K) (Q := Q) (E := E) (H := H) (C := C) (P := P)
      (N := N) (lowerUpper := lowerUpper) (realSeal := realSeal) (bundle := bundle)
      (pkg := pkg) routeLU routeKQ routeEC unaryL unaryU unaryQ unaryC realPkg
  have carrierN :
      hsame N N ∧
        List.Mem
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist K)
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow
            (DedekindMacNeilleCompletionUp.mk L U K Q E H C P N)) :=
    ⟨hsame_refl N, closure.right.right.right.right.right.right.right⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N carrierN
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        cases sourceH with
        | intro sameHN member =>
            exact ⟨hsame_trans (hsame_symm sameHK) sameHN, member⟩
    }
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact source.left
  }

end BEDC.Derived.DedekindMacNeilleCompletionUp
