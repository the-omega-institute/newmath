import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathConfluenceFrontierPublicHandoff [AskSetup] [PackageSetup]
    {S N O U D H C P L confluence frontier publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket S N O U D H C P L bundle pkg ->
      Cont U C confluence ->
        Cont confluence D frontier ->
          Cont frontier L publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row D ∨ hsame row frontier ∨
                      Cont frontier L publicRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg ∧
                      hsame row publicRead)
                  hsame ∧
                UnaryHistory confluence ∧ UnaryHistory frontier ∧
                  UnaryHistory publicRead ∧ Cont U C confluence ∧
                    Cont confluence D frontier ∧ Cont frontier L publicRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet confluenceRoute frontierRoute publicRoute publicPkg
  obtain ⟨_SUnary, _NUnary, _OUnary, UUnary, DUnary, _HUnary, CUnary,
    _PUnary, LUnary, _snRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have confluenceUnary : UnaryHistory confluence :=
    unary_cont_closed UUnary CUnary confluenceRoute
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed confluenceUnary DUnary frontierRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed frontierUnary LUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row D ∨ hsame row frontier ∨ Cont frontier L publicRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr publicRoute))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, publicPkg, source.left⟩
  }
  exact
    ⟨cert, confluenceUnary, frontierUnary, publicUnary, confluenceRoute, frontierRoute,
      publicRoute⟩

end BEDC.Derived.MetaCICCriticalPathUp
