import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N approxRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory A ->
        UnaryHistory L ->
          UnaryHistory T ->
            UnaryHistory E ->
              Cont B A M ->
                Cont M L S ->
                  Cont S T G ->
                    Cont G E approxRead ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row approxRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                                hsame row T ∨ hsame row S ∨ hsame row G ∨ hsame row E ∨
                                  hsame row approxRead ∨ hsame row N)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧ Cont S T G ∧
                                Cont G E approxRead ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory G ∧
                            UnaryHistory approxRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro boundaryUnary adjacencyUnary levelUnary toleranceUnary sealUnary boundaryRoute
    levelRoute toleranceRoute approximationRoute packageN
  have mediantUnary : UnaryHistory M :=
    unary_cont_closed boundaryUnary adjacencyUnary boundaryRoute
  have sternBrocotUnary : UnaryHistory S :=
    unary_cont_closed mediantUnary levelUnary levelRoute
  have approximationUnary : UnaryHistory G :=
    unary_cont_closed sternBrocotUnary toleranceUnary toleranceRoute
  have approxReadUnary : UnaryHistory approxRead :=
    unary_cont_closed approximationUnary sealUnary approximationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row approxRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row S ∨ hsame row G ∨ hsame row E ∨ hsame row approxRead ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧ Cont S T G ∧
              Cont G E approxRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro approxRead ⟨hsame_refl approxRead, approxReadUnary⟩
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
                  (Or.inr
                    (Or.inr (Or.inr (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, levelRoute, toleranceRoute, approximationRoute,
          packageN⟩
  }
  exact ⟨cert, mediantUnary, sternBrocotUnary, approximationUnary, approxReadUnary⟩

theorem FareySequenceNameCertObligations [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory A →
        UnaryHistory M →
          UnaryHistory L →
            UnaryHistory T →
              UnaryHistory S →
                UnaryHistory D →
                  UnaryHistory Q →
                    UnaryHistory W →
                      UnaryHistory R →
                        UnaryHistory G →
                          UnaryHistory E →
                            UnaryHistory H →
                              UnaryHistory C →
                                UnaryHistory P →
                                  UnaryHistory N →
                                    Cont B A route →
                                      PkgSig bundle P pkg →
                                        PkgSig bundle N pkg →
                                          SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row B ∨ hsame row A ∨ hsame row M ∨
                                                hsame row L ∨ hsame row T ∨ hsame row S ∨
                                                  hsame row D ∨ hsame row Q ∨
                                                    hsame row W ∨ hsame row R ∨
                                                      hsame row G ∨ hsame row E ∨
                                                        hsame row H ∨ hsame row C ∨
                                                          hsame row P ∨ hsame row N ∨
                                                            hsame row route)
                                            (fun row : BHist => UnaryHistory row)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                (PkgSig bundle P pkg ∧ PkgSig bundle N pkg))
                                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro unaryB unaryA unaryM unaryL unaryT unaryS unaryD unaryQ unaryW unaryR unaryG
    unaryE unaryH unaryC unaryP unaryN routeCont pkgP pkgN
  have routeUnary : UnaryHistory route :=
    unary_cont_closed unaryB unaryA routeCont
  have sourceRoute :
      (fun row : BHist =>
        hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
          hsame row S ∨ hsame row D ∨ hsame row Q ∨ hsame row W ∨ hsame row R ∨
            hsame row G ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row route) route := by
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
    right
    right
    right
    right
    right
    right
    exact hsame_refl route
  have source_unary :
      ∀ {row : BHist},
        (hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
          hsame row S ∨ hsame row D ∨ hsame row Q ∨ hsame row W ∨ hsame row R ∨
            hsame row G ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row route) →
          UnaryHistory row := by
    intro row source
    cases source with
    | inl sameB => exact unary_transport_symm unaryB sameB
    | inr rest =>
        cases rest with
        | inl sameA => exact unary_transport_symm unaryA sameA
        | inr rest =>
            cases rest with
            | inl sameM => exact unary_transport_symm unaryM sameM
            | inr rest =>
                cases rest with
                | inl sameL => exact unary_transport_symm unaryL sameL
                | inr rest =>
                    cases rest with
                    | inl sameT => exact unary_transport_symm unaryT sameT
                    | inr rest =>
                        cases rest with
                        | inl sameS => exact unary_transport_symm unaryS sameS
                        | inr rest =>
                            cases rest with
                            | inl sameD => exact unary_transport_symm unaryD sameD
                            | inr rest =>
                                cases rest with
                                | inl sameQ => exact unary_transport_symm unaryQ sameQ
                                | inr rest =>
                                    cases rest with
                                    | inl sameW => exact unary_transport_symm unaryW sameW
                                    | inr rest =>
                                        cases rest with
                                        | inl sameR => exact unary_transport_symm unaryR sameR
                                        | inr rest =>
                                            cases rest with
                                            | inl sameG => exact unary_transport_symm unaryG sameG
                                            | inr rest =>
                                                cases rest with
                                                | inl sameE =>
                                                    exact unary_transport_symm unaryE sameE
                                                | inr rest =>
                                                    cases rest with
                                                    | inl sameH =>
                                                        exact unary_transport_symm unaryH sameH
                                                    | inr rest =>
                                                        cases rest with
                                                        | inl sameC =>
                                                            exact
                                                              unary_transport_symm unaryC sameC
                                                        | inr rest =>
                                                            cases rest with
                                                            | inl sameP =>
                                                                exact
                                                                  unary_transport_symm unaryP sameP
                                                            | inr rest =>
                                                                cases rest with
                                                                | inl sameN =>
                                                                    exact
                                                                      unary_transport_symm
                                                                        unaryN sameN
                                                                | inr sameRoute =>
                                                                    exact
                                                                      unary_transport_symm
                                                                        routeUnary sameRoute
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

end BEDC.Derived.FareySequenceUp
