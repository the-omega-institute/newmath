import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetNameCertObligations [AskSetup] [PackageSetup]
    {T G I D R E H K P N route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory G →
        UnaryHistory I →
          UnaryHistory D →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory K →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont T G route →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row G ∨ hsame row I ∨
                                    hsame row D ∨ hsame row R ∨ hsame row E ∨
                                      hsame row H ∨ hsame row K ∨ hsame row P ∨
                                        hsame row N ∨ hsame row route)
                                (fun row : BHist => UnaryHistory row)
                                (fun row : BHist =>
                                  UnaryHistory row ∧
                                    (PkgSig bundle P pkg ∧ PkgSig bundle N pkg))
                                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro unaryT unaryG unaryI unaryD unaryR unaryE unaryH unaryK unaryP unaryN routeCont
    pkgP pkgN
  have routeUnary : UnaryHistory route :=
    unary_cont_closed unaryT unaryG routeCont
  have sourceRoute :
      (fun row : BHist =>
        hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
          hsame row E ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
            hsame row route) route := by
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    exact hsame_refl route
  have source_unary :
      ∀ {row : BHist},
        (hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
          hsame row E ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
            hsame row route) →
          UnaryHistory row := by
    intro row source
    cases source with
    | inl sameT => exact unary_transport_symm unaryT sameT
    | inr rest =>
        cases rest with
        | inl sameG => exact unary_transport_symm unaryG sameG
        | inr rest =>
            cases rest with
            | inl sameI => exact unary_transport_symm unaryI sameI
            | inr rest =>
                cases rest with
                | inl sameD => exact unary_transport_symm unaryD sameD
                | inr rest =>
                    cases rest with
                    | inl sameR => exact unary_transport_symm unaryR sameR
                    | inr rest =>
                        cases rest with
                        | inl sameE => exact unary_transport_symm unaryE sameE
                        | inr rest =>
                            cases rest with
                            | inl sameH => exact unary_transport_symm unaryH sameH
                            | inr rest =>
                                cases rest with
                                | inl sameK => exact unary_transport_symm unaryK sameK
                                | inr rest =>
                                    cases rest with
                                    | inl sameP => exact unary_transport_symm unaryP sameP
                                    | inr rest =>
                                        cases rest with
                                        | inl sameN => exact unary_transport_symm unaryN sameN
                                        | inr sameRoute =>
                                            exact unary_transport_symm routeUnary sameRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro route sourceRoute
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
        intro row other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source_unary source
    ledger_sound := by
      intro _row source
      exact ⟨source_unary source, pkgP, pkgN⟩
  }

end BEDC.Derived.CantorSetUp
