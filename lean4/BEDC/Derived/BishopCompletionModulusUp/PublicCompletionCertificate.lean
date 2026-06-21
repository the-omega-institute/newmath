import BEDC.Derived.BishopCompletionModulusUp.TasteGate

namespace BEDC.Derived.BishopCompletionModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionModulusCarrier_public_completion_certificate [AskSetup] [PackageSetup]
    {M S n k W D R E H C P N request refinedK refinedW refinedR sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionModulusCarrier M S n k W D R E H C P N bundle pkg ->
      UnaryHistory request ->
        hsame request n ->
          Cont M request refinedK ->
            Cont S refinedK refinedW ->
              Cont refinedW D refinedR ->
                Cont refinedR E sealRead ->
                  SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row S ∨ hsame row request ∨
                        hsame row refinedK ∨ hsame row refinedW ∨ hsame row D ∨
                          hsame row refinedR ∨ hsame row E ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M request refinedK ∧
                        Cont S refinedK refinedW ∧ Cont refinedW D refinedR ∧
                          Cont refinedR E sealRead ∧ PkgSig bundle P pkg)
                    hsame ∧ UnaryHistory request ∧ UnaryHistory refinedK ∧
                      UnaryHistory refinedW ∧ UnaryHistory refinedR ∧
                        UnaryHistory sealRead ∧ hsame refinedK k ∧ hsame refinedR R ∧
                          hsame sealRead H ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier requestUnary sameRequest refinedModulusRoute refinedWindowRoute
    refinedRegularRoute refinedSealRoute
  have routeFacts :=
    BishopCompletionModulusCarrier_finite_threshold_induction
      (M := M) (S := S) (n := n) (k := k) (W := W) (D := D) (R := R)
      (E := E) (H := H) (C := C) (P := P) (N := N) (request := request)
      (refinedK := refinedK) (refinedW := refinedW) (refinedR := refinedR)
      (sealRead := sealRead) (bundle := bundle) (pkg := pkg)
      carrier requestUnary sameRequest refinedModulusRoute refinedWindowRoute
      refinedRegularRoute refinedSealRoute
  obtain ⟨requestUnary', refinedKUnary, refinedWUnary, refinedRUnary, sealReadUnary,
    sameRefinedK, sameRefinedR, sameSealRead, provenancePkg⟩ := routeFacts
  have scope :=
    BishopCompletionModulusCarrier_scope_closure
      (M := M) (S := S) (n := n) (k := k) (W := W) (D := D) (R := R)
      (E := E) (H := H) (C := C) (P := P) (N := N) (request := request)
      (refinedK := refinedK) (refinedW := refinedW) (refinedR := refinedR)
      (sealRead := sealRead) (bundle := bundle) (pkg := pkg)
      carrier requestUnary sameRequest refinedModulusRoute refinedWindowRoute
      refinedRegularRoute refinedSealRoute
  exact
    ⟨scope.left, requestUnary', refinedKUnary, refinedWUnary, refinedRUnary,
      sealReadUnary, sameRefinedK, sameRefinedR, sameSealRead, provenancePkg⟩

end BEDC.Derived.BishopCompletionModulusUp
