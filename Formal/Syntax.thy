theory Syntax imports Main
begin


lemma simplImpl: "A \<longrightarrow> A"
apply (rule impI)
apply assumption
  done


type_synonym name = string

(* See grammar l. 192 *)
datatype value_type 
  = LongVT | DoubleVT | StringVT | BooleanVT | DatetimeVT 

(* See grammar l. 189 *)
datatype native_type 
  = Attribute
  | Entity
  | Relation
  | Role
  (* TODO: Thing type excluded.
     It occurs in the grammar but not clear how to use it.
  | Thing
*)

datatype tp 
  = NativeTp native_type
  | ValueTp value_type
  | NamedTp name

(* See grammar l. 114 ff 
   TODO: incomplete; missing: Abstract, Regex, Subx, Then, Type, When
*)
datatype tp_rel 
  = Owns | Plays | Relates | Sub

(* The context is meant to be constructed in a stack-wise fashion, 
  with decreasing recency from right to left.
 *)
datatype ctxt_def 
  = Ctxt_def tp tp_rel tp
  | Ctxt_plays_def tp tp tp

type_synonym ctxt = "ctxt_def list"


(* or should this only be a name set  *)


(* Declaration of attributes *)
definition attribute_decls :: "ctxt => tp set" where
"attribute_decls c = {}"
(* Declaration of entities *)
definition entity_decls :: "ctxt => tp set" where
"entity_decls c = {}"
(* Declaration of relations *)
definition relation_decls :: "ctxt => tp set" where
"relation_decls c = {}"
(* Declaration of roles *)
definition role_decls :: "ctxt => tp set" where
"role_decls c = {}"

(* Declared names (for whatever kind) *)
definition declared_names :: "ctxt => name set" where
"declared_names c = {}"

inductive wf_ctxt :: "ctxt => bool" where
wf_empty: "wf_ctxt []"
|
(* Of the form:  serial_num sub attribute *)
wf_sub_attribute: "wf_ctxt c 
\<Longrightarrow> nt \<notin> declared_names c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt) Sub (NativeTp Attribute)) # c )"
(* TODO: open question: is there a transitive subtyping of attributes? *)
|
(* Of the form:  a_entity sub entity *)
wf_sub_entity: "wf_ctxt c 
\<Longrightarrow> nt \<notin> declared_names c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt) Sub (NativeTp Entity)) # c )"
|
(* Of the form:  a_sub_entity sub a_entity *)
wf_sub_entity_trans: "wf_ctxt c 
\<Longrightarrow> nt1 \<notin> declared_names c
\<Longrightarrow> NamedTp nt2 \<in> entity_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt1) Sub (NamedTp nt2)) # c )"
|
(* Of the form:  r_relation sub relation *)
wf_sub_relation: "wf_ctxt c 
\<Longrightarrow> nt \<notin> declared_names c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt) Sub (NativeTp Relation)) # c )"
|
(* Of the form:  r_sub_relation sub r_relation *)
wf_sub_relation_trans: "wf_ctxt c 
\<Longrightarrow> nt1 \<notin> declared_names c
\<Longrightarrow> NamedTp nt2 \<in> relation_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt1) Sub (NamedTp nt2)) # c )"

(* no subtyping roles *)

|
(* Of the form:  a_entity owns serial_num *)
wf_owns_entity: "wf_ctxt c 
\<Longrightarrow> NamedTp et \<in> entity_decls c
\<Longrightarrow> NamedTp at \<in> attribute_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp et) Owns (NamedTp at)) # c )"

|
(* Of the form:  r_relation owns serial_num *)
wf_owns_relation: "wf_ctxt c 
\<Longrightarrow> NamedTp rt \<in> entity_decls c
\<Longrightarrow> NamedTp at \<in> attribute_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp rt) Owns (NamedTp at)) # c )"


|
(* Surprisingly, the role type is not constrained, 
   i.e. can be a previously declared entity or relation type *)
(* Of the form:  r_relation relates r_role *)
wf_relates: "wf_ctxt c 
\<Longrightarrow> NamedTp relt \<in> relation_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp relt) Relates (NamedTp rolet)) # c )"

|
(* Of the form:  a_entity plays r_relation:r_role *)
(* TODO: the Plays relation is the only ternary one, which complicates the type structure.
  Besides, a role name has to be globally unique; differently said, the same role name 
  cannot be attached to two different relations, such as in 
  r_relation relates b_role; s_relation  relates b_role;
  Therefore, writing b_entity plays r_relation:b_role; 
  is redundant because b_role already uniquely identifies r_relation.
  It would be enough to write b_entity plays b_role;
 *)
(* Surprisingly:
   - et is not resticted to be: NamedTp et \<in> entity_decls c
    *)
wf_plays: "wf_ctxt c 
\<Longrightarrow> NamedTp relt \<in> relation_decls c
\<Longrightarrow> NamedTp rolet \<in> role_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_plays_def (NamedTp et) (NamedTp relt) (NamedTp rolet)) # c )"

|
(* Of the form:  serial_num value long *)
wf_value: "wf_ctxt c 
\<Longrightarrow> NamedTp at \<in> attribute_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp at) Value (NativeTp bt)) # c )"

end