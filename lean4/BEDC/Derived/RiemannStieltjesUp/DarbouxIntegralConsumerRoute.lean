import BEDC.Derived.RiemannStieltjesUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RiemannStieltjesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannStieltjesDarbouxIntegralConsumerRoute [AskSetup] [PackageSetup]
    {integrand variation tagged step handoff realSeal transport replay provenance localName meshRead
      darbouxRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont variation tagged meshRead →
      Cont meshRead step handoff →
        Cont handoff realSeal darbouxRead →
          hsame transport replay →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                UnaryHistory variation →
                  UnaryHistory tagged →
                    UnaryHistory step →
                      UnaryHistory realSeal →
                        UnaryHistory replay →
                          SemanticNameCert
                              (fun row : BHist => hsame row darbouxRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row integrand ∨ hsame row variation ∨
                                  hsame row tagged ∨ hsame row step ∨ hsame row handoff ∨
                                    hsame row realSeal ∨ hsame row darbouxRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont variation tagged meshRead ∧
                                  Cont meshRead step handoff ∧
                                    Cont handoff realSeal darbouxRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory meshRead ∧ UnaryHistory handoff ∧
                              UnaryHistory darbouxRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro meshRoute handoffRoute darbouxRoute _transportReplay provenancePkg localNamePkg
    variationUnary taggedUnary stepUnary realSealUnary _replayUnary
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed variationUnary taggedUnary meshRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed meshUnary stepUnary handoffRoute
  have darbouxUnary : UnaryHistory darbouxRead :=
    unary_cont_closed handoffUnary realSealUnary darbouxRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row darbouxRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row integrand ∨ hsame row variation ∨ hsame row tagged ∨
              hsame row step ∨ hsame row handoff ∨ hsame row realSeal ∨
                hsame row darbouxRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont variation tagged meshRead ∧ Cont meshRead step handoff ∧
              Cont handoff realSeal darbouxRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro darbouxRead ⟨hsame_refl darbouxRead, darbouxUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, meshRoute, handoffRoute, darbouxRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, meshUnary, handoffUnary, darbouxUnary⟩

end BEDC.Derived.RiemannStieltjesUp
