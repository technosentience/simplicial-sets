import algebraic_topology.simplicial_object
import algebra.category.Group.basic
import kan_complex

universes v u

open category_theory

open_locale simplicial

@[derive [large_category]]
def sGrp := simplicial_object Group

def to_sSet : sGrp ⥤ sSet := (simplicial_object.whiskering _ _).obj (forget Group)

def sGrp_Kan (G : sGrp) : is_kan_complex (to_sSet.obj G) :=
begin
  intros n i f,
  fconstructor,
  fconstructor,
  sorry,
  sorry
end

