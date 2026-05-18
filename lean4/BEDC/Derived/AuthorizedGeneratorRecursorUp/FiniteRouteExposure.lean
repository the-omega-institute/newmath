import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert
import BEDC.FKernel.Sig

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorFiniteRouteExposure [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont M B descentRead ->
          Cont D O outputRead ->
            Cont outputRead A auditRead ->
              Cont auditRead C publicRead ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row N ∧
                          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N
                            bundle pkg)
                      (fun row : BHist =>
                        hsame row N ∧ Cont I E branchRead ∧ Cont M B descentRead ∧
                          Cont D O outputRead ∧ Cont outputRead A auditRead ∧
                            Cont auditRead C publicRead)
                      (fun row : BHist =>
                        hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier branchRoute descentRoute outputRoute auditRoute publicRoute publicPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
      provenanceUnary, unaryG, unaryN, carrierBranch, carrierDescent, carrierOutput,
      transportSame, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed unaryM unaryB descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryD unaryO outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryA auditRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary unaryC publicRoute
  have carrierWitness :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
        provenanceUnary, unaryG, unaryN, carrierBranch, carrierDescent, carrierOutput,
        transportSame, provenancePkg⟩
  have sourceName :
      (fun row : BHist =>
        hsame row N ∧
          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg) N := by
    exact ⟨hsame_refl N, carrierWitness⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg)
          (fun row : BHist =>
            hsame row N ∧ Cont I E branchRead ∧ Cont M B descentRead ∧
              Cont D O outputRead ∧ Cont outputRead A auditRead ∧
                Cont auditRead C publicRead)
          (fun row : BHist =>
            hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceName
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, branchRoute, descentRoute, outputRoute, auditRoute, publicRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, publicPkg⟩
    }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
