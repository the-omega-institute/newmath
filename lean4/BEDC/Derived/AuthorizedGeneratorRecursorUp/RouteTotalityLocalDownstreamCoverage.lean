import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_route_totality_local_downstream_coverage
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N routeRead outputRead coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont H C routeRead →
        Cont O A outputRead →
          Cont routeRead outputRead coverageRead →
            PkgSig bundle coverageRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨
                      hsame row D ∨ hsame row O ∨ hsame row A ∨ hsame row coverageRead)
                  (fun row : BHist =>
                    hsame row coverageRead ∧ PkgSig bundle coverageRead pkg)
                  hsame ∧
                UnaryHistory routeRead ∧ UnaryHistory outputRead ∧
                  UnaryHistory coverageRead ∧ Cont H C routeRead ∧
                    Cont O A outputRead ∧ Cont routeRead outputRead coverageRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier routeRoute outputRoute coverageRoute coveragePkg
  obtain ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, unaryH,
    unaryC, _unaryP, _unaryG, _unaryN, _carrierMotive, _carrierDescent,
    _carrierOutput, _transportSame, _provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryH unaryC routeRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed routeUnary outputUnary coverageRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨
              hsame row D ∨ hsame row O ∨ hsame row A ∨ hsame row coverageRead)
          (fun row : BHist => hsame row coverageRead ∧ PkgSig bundle coverageRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro coverageRead ⟨hsame_refl coverageRead, coverageUnary⟩
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, coveragePkg⟩
    }
  exact
    ⟨cert, routeUnary, outputUnary, coverageUnary, routeRoute, outputRoute, coverageRoute⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
