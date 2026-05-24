import BEDC.Derived.FiniteRealSectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FiniteRealSection_route_consumer_exactness [AskSetup] [PackageSetup]
    {q W R D E H C P N qW qWR qWRD qWRDE terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory N → Cont q W qW → Cont qW R qWR →
        Cont qWR D qWRD → Cont qWRD E qWRDE → Cont qWRDE N terminal →
          PkgSig bundle terminal pkg →
            FieldFaithful.fields (FiniteRealSectionUp.mk q W R D E H C P N) =
                [q, W, R, D, E, H, C, P, N] ∧
              UnaryHistory terminal ∧
                SemanticNameCert
                  (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row qW ∨ hsame row qWR ∨ hsame row qWRD ∨
                      hsame row qWRDE ∨ hsame row terminal)
                  (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryQ unaryW unaryR unaryD unaryE unaryN requestWindow windowReadback
    readbackTolerance toleranceSeal sealTerminal terminalPkg
  have requestWindowUnary : UnaryHistory qW :=
    unary_cont_closed unaryQ unaryW requestWindow
  have windowReadbackUnary : UnaryHistory qWR :=
    unary_cont_closed requestWindowUnary unaryR windowReadback
  have readbackToleranceUnary : UnaryHistory qWRD :=
    unary_cont_closed windowReadbackUnary unaryD readbackTolerance
  have toleranceSealUnary : UnaryHistory qWRDE :=
    unary_cont_closed readbackToleranceUnary unaryE toleranceSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed toleranceSealUnary unaryN sealTerminal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row qW ∨ hsame row qWR ∨ hsame row qWRD ∨ hsame row qWRDE ∨
            hsame row terminal)
        (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal ⟨hsame_refl terminal, terminalUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg⟩
  }
  exact ⟨rfl, terminalUnary, cert⟩

theorem FiniteRealSection_obligation_surface [AskSetup] [PackageSetup]
    {q W R D E H C P N qW qWR qWRD qWRDE terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory H → UnaryHistory C → UnaryHistory P →
        UnaryHistory N → Cont q W qW → Cont qW R qWR → Cont qWR D qWRD →
          Cont qWRD E qWRDE → Cont qWRDE N terminal → PkgSig bundle terminal pkg →
            FieldFaithful.fields (FiniteRealSectionUp.mk q W R D E H C P N) =
                [q, W, R, D, E, H, C, P, N] ∧
              UnaryHistory terminal ∧
                SemanticNameCert
                  (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row qW ∨ hsame row qWR ∨ hsame row qWRD ∨
                      hsame row qWRDE ∨ hsame row terminal)
                  (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryQ unaryW unaryR unaryD unaryE _unaryH _unaryC _unaryP unaryN
    requestWindow windowReadback readbackTolerance toleranceSeal sealTerminal terminalPkg
  exact
    FiniteRealSection_route_consumer_exactness unaryQ unaryW unaryR unaryD unaryE unaryN
      requestWindow windowReadback readbackTolerance toleranceSeal sealTerminal terminalPkg

theorem FiniteRealSection_nonescape [AskSetup] [PackageSetup]
    {q W R D E H C P N qW qWR qWRD qWRDE terminal ambient : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory N → Cont q W qW → Cont qW R qWR →
        Cont qWR D qWRD → Cont qWRD E qWRDE → Cont qWRDE N terminal →
          PkgSig bundle terminal pkg → hsame ambient (BHist.e0 terminal) →
            FieldFaithful.fields (FiniteRealSectionUp.mk q W R D E H C P N) =
                [q, W, R, D, E, H, C, P, N] ∧
              UnaryHistory terminal ∧
                SemanticNameCert
                  (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row qW ∨ hsame row qWR ∨ hsame row qWRD ∨
                      hsame row qWRDE ∨ hsame row terminal)
                  (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
                  hsame ∧
                    (hsame ambient terminal → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryQ unaryW unaryR unaryD unaryE unaryN requestWindow windowReadback
    readbackTolerance toleranceSeal sealTerminal terminalPkg ambientExtended
  have route :=
    FiniteRealSection_route_consumer_exactness (H := H) (C := C) (P := P)
      unaryQ unaryW unaryR unaryD unaryE unaryN requestWindow windowReadback
      readbackTolerance toleranceSeal sealTerminal terminalPkg
  refine ⟨route.left, route.right.left, route.right.right, ?_⟩
  intro ambientTerminal
  exact hsame_extension_self_absurd.left terminal
    (hsame_trans (hsame_symm ambientExtended) ambientTerminal)

end BEDC.Derived.FiniteRealSectionUp
