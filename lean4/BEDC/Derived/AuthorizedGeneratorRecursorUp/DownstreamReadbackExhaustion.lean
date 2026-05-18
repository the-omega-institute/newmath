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

theorem AuthorizedGeneratorRecursorDownstreamReadbackExhaustion [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead publicRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C publicRead ->
          Cont publicRead N downstreamRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row downstreamRead ∧ Cont I E M ∧ Cont M B D ∧
                      Cont D O A ∧ Cont O A outputRead ∧
                        Cont outputRead C publicRead ∧ Cont publicRead N downstreamRead ∧
                          hsame H (append A C))
                  (fun row : BHist =>
                    hsame row downstreamRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                  UnaryHistory downstreamRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputRoute publicRoute downstreamRoute publicPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      unaryC, carrierPkg, _unaryG, unaryN, carrierBranch, carrierDescent,
      carrierOutput, transportSame, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary unaryC publicRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed publicUnary unaryN downstreamRoute
  have sourceDownstream :
      (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row) downstreamRead := by
    exact ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont I E M ∧ Cont M B D ∧
              Cont D O A ∧ Cont O A outputRead ∧ Cont outputRead C publicRead ∧
                Cont publicRead N downstreamRead ∧ hsame H (append A C))
          (fun row : BHist =>
            hsame row downstreamRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro downstreamRead sourceDownstream
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
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, carrierBranch, carrierDescent, carrierOutput, outputRoute,
            publicRoute, downstreamRoute, transportSame⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, publicPkg⟩
    }
  exact ⟨cert, outputUnary, publicUnary, downstreamUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
