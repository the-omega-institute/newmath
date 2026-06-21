import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeKernelMembershipObligation [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N qRead iRead rRead eRead hRead cRead pRead nRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont M Q qRead ->
                          Cont qRead I iRead ->
                            Cont iRead R rRead ->
                              Cont rRead E eRead ->
                                Cont eRead H hRead ->
                                  Cont hRead C cRead ->
                                    Cont cRead P pRead ->
                                      Cont pRead N nRead ->
                                        PkgSig bundle P pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row nRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row M ∨ hsame row Q ∨
                                                  hsame row I ∨ hsame row R ∨
                                                    hsame row E ∨ hsame row H ∨
                                                      hsame row C ∨ hsame row P ∨
                                                        hsame row N ∨ hsame row nRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont M Q qRead ∧
                                                  Cont qRead I iRead ∧
                                                    Cont iRead R rRead ∧
                                                      Cont rRead E eRead ∧
                                                        Cont eRead H hRead ∧
                                                          Cont hRead C cRead ∧
                                                            Cont cRead P pRead ∧
                                                              Cont pRead N nRead ∧
                                                                PkgSig bundle P pkg)
                                              hsame ∧
                                            UnaryHistory qRead ∧ UnaryHistory iRead ∧
                                              UnaryHistory rRead ∧ UnaryHistory eRead ∧
                                                UnaryHistory hRead ∧ UnaryHistory cRead ∧
                                                  UnaryHistory pRead ∧
                                                    UnaryHistory nRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields unaryM unaryQ unaryI unaryR unaryE unaryH unaryC unaryP unaryN routeMQ
    routeQI routeIR routeRE routeEH routeHC routeCP routePN packageP
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have unaryQRead : UnaryHistory qRead := unary_cont_closed unaryM unaryQ routeMQ
  have unaryIRead : UnaryHistory iRead := unary_cont_closed unaryQRead unaryI routeQI
  have unaryRRead : UnaryHistory rRead := unary_cont_closed unaryIRead unaryR routeIR
  have unaryERead : UnaryHistory eRead := unary_cont_closed unaryRRead unaryE routeRE
  have unaryHRead : UnaryHistory hRead := unary_cont_closed unaryERead unaryH routeEH
  have unaryCRead : UnaryHistory cRead := unary_cont_closed unaryHRead unaryC routeHC
  have unaryPRead : UnaryHistory pRead := unary_cont_closed unaryCRead unaryP routeCP
  have unaryNRead : UnaryHistory nRead := unary_cont_closed unaryPRead unaryN routePN
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row nRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q qRead ∧ Cont qRead I iRead ∧
              Cont iRead R rRead ∧ Cont rRead E eRead ∧ Cont eRead H hRead ∧
                Cont hRead C cRead ∧ Cont cRead P pRead ∧ Cont pRead N nRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nRead
        (And.intro (hsame_refl nRead) unaryNRead)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeMQ, routeQI, routeIR, routeRE, routeEH, routeHC, routeCP,
          routePN, packageP⟩
  }
  exact
    ⟨cert, unaryQRead, unaryIRead, unaryRRead, unaryERead, unaryHRead, unaryCRead,
      unaryPRead, unaryNRead⟩

end BEDC.Derived.SetlikeUp
