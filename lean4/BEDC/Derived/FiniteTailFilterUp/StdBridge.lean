import BEDC.Derived.FiniteTailFilterUp.BridgePremiseSurface

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterUp_StdBridge [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead completionRead premiseRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRead ->
        Cont sealRead H realWindowRead ->
          UnaryHistory C ->
            Cont realWindowRead C completionRead ->
              Cont completionRead N premiseRead ->
                UnaryHistory P ->
                  Cont premiseRead P publicRead ->
                    PkgSig bundle publicRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row sealRead ∨ hsame row realWindowRead ∨
                              hsame row completionRead ∨ hsame row premiseRead ∨
                                hsame row publicRead)
                          (fun row : BHist =>
                            hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sealRoute realWindowRoute unaryC completionRoute premiseRoute unaryP
    publicRoute publicPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _unaryCarrierC, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryCompletion : UnaryHistory completionRead :=
    unary_cont_closed unaryRealWindow unaryC completionRoute
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have unaryPremise : UnaryHistory premiseRead :=
    unary_cont_closed unaryCompletion unaryN premiseRoute
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryPremise unaryP publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sealRead ∨ hsame row realWindowRead ∨
              hsame row completionRead ∨ hsame row premiseRead ∨ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublic⟩
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
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg⟩
  }
  exact ⟨cert, unaryPublic⟩

end BEDC.Derived.FiniteTailFilterUp
