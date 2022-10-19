
section \<open> Syntax \label{sec:syntax} \<close>
theory Syntax imports Main
begin

subsection \<open> Syntactic elements \label{sec:syntactic_elements} \<close>

text \<open> Basic concepts \<close>

type_synonym name = string

text \<open>  See grammar l. 192 \<close>
datatype value_type 
  = LongVT | DoubleVT | StringVT | BooleanVT | DatetimeVT 

text \<open> See grammar l. 189  \<close>
text  \<open> Thing type not used, see \issueref{issue:thing_type} \<close>
datatype native_type 
  = Attribute
  | Entity
  | Relation
  | Role
  | Thing

datatype tp 
  = NativeTp native_type
  | ValueTp value_type
  | NamedTp name

text \<open> See grammar l. 114 ff 
   TODO: incomplete; missing: Abstract, Regex, Subx, Then, Type, When \<close>

datatype tp_rel 
  = Owns | Plays | Relates | Sub | Value

subsection \<open> Typing context \label{sec:typing_context} \<close>

text \<open> The context is meant to be constructed in a stack-wise fashion, 
  with decreasing recency from right to left. \<close>

datatype ctxt_def 
  = Ctxt_def tp tp_rel tp
  | Ctxt_plays_def tp tp tp

type_synonym ctxt = "ctxt_def list"

(* or should this only be a name set  *)


(* Declaration of roles *)
definition role_decls :: "ctxt => tp set" where
"role_decls c = {}"

text \<open>Declared names (for whatever kind) \<close>
definition declared_names :: "ctxt => name set" where
"declared_names c = {n. \<exists> r t. Ctxt_def (NamedTp n) r t \<in> set c }"


text \<open> Check if, in a context, a name is (directly or transitively) 
of a kind / native type, such as Entity, Relation \<close>

inductive decl_of_kind :: "ctxt => name => native_type => bool" where
decl_of_kind_base: 
   "decl_of_kind ((Ctxt_def (NamedTp n) Sub (NativeTp k)) # c) n k"
|
decl_of_kind_step_same: 
   "decl_of_kind c n2 k
\<Longrightarrow> decl_of_kind ((Ctxt_def (NamedTp n) Sub (NamedTp n2)) # c) n k"
|
decl_of_kind_step_other: 
   "n1 \<noteq> n
\<Longrightarrow> decl_of_kind c n2 k
\<Longrightarrow> decl_of_kind ((Ctxt_def (NamedTp n1) Sub (NamedTp n2)) # c) n k"

text \<open> Well-formedness of a context, defined inductively in the style of Prolog rules. \<close>

inductive wf_ctxt :: "ctxt => bool" where
\<comment> \<open> Empty context is wellformed \<close>
wf_empty: "wf_ctxt []"
|
\<comment> \<open> Of the form:  \texttt{serial\_num sub attribute}.
   This declaration seems redundant, see \issueref{issue:decl_attribute}.
   Also not clear: is there a transitive subtyping of attributes?  \<close>
wf_sub_attribute: "wf_ctxt c 
\<Longrightarrow> nt \<notin> declared_names c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt) Sub (NativeTp Attribute)) # c )"
|
\<comment> \<open>  Of the form:  \texttt{a\_entity sub entity} \<close>
wf_sub_entity: "wf_ctxt c 
\<Longrightarrow> nt \<notin> declared_names c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt) Sub (NativeTp Entity)) # c )"
|
\<comment> \<open> Of the form:  \texttt{a\_sub\_entity sub a\_entity} \<close>
wf_sub_entity_trans: "wf_ctxt c 
\<Longrightarrow> nt1 \<notin> declared_names c
\<Longrightarrow> decl_of_kind c nt2 Entity
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt1) Sub (NamedTp nt2)) # c )"
|
\<comment> \<open> Of the form:  \texttt{r\_relation sub relation}  \<close>
wf_sub_relation: "wf_ctxt c 
\<Longrightarrow> nt \<notin> declared_names c
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt) Sub (NativeTp Relation)) # c )"
|
\<comment> \<open> Of the form:  \texttt{r\_sub\_relation sub r\_relation}  \<close>
wf_sub_relation_trans: "wf_ctxt c 
\<Longrightarrow> nt1 \<notin> declared_names c
\<Longrightarrow> decl_of_kind c nt2 Relation
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp nt1) Sub (NamedTp nt2)) # c )"

\<comment> \<open> no subtyping roles \<close>

|
\<comment> \<open> Of the form:  \texttt{a\_entity owns serial\_num}  \<close>
wf_owns_entity: "wf_ctxt c 
\<Longrightarrow> decl_of_kind c et Entity
\<Longrightarrow> decl_of_kind c at Attribute
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp et) Owns (NamedTp at)) # c )"
|
\<comment> \<open>Of the form:  \texttt{r\_relation owns serial\_num} \<close>
wf_owns_relation: "wf_ctxt c 
\<Longrightarrow> decl_of_kind c rt Entity
\<Longrightarrow> decl_of_kind c at Attribute
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp rt) Owns (NamedTp at)) # c )"
|
(* Surprisingly, the role type is not constrained, 
   i.e. can be a previously declared entity or relation type *)
\<comment> \<open>Of the form:  \texttt{r\_relation relates r\_role} \<close>
wf_relates: "wf_ctxt c 
\<Longrightarrow> decl_of_kind c relt Relation
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp relt) Relates (NamedTp rolet)) # c )"
|
\<comment> \<open> Of the form:  \texttt{a\_entity plays r\_relation:r\_role} \<close>
(* TODO: the Plays relation is the only ternary one, which complicates the type structure.
  Besides, a role name has to be globally unique; differently said, the same role name 
  cannot be attached to two different relations, such as in 
  r_relation relates b_role; s_relation  relates b_role;
  Therefore, writing b_entity plays r_relation:b_role; 
  is redundant because b_role already uniquely identifies r_relation.
  It would be enough to write b_entity plays b_role; *)
 (* Surprisingly:
   - et is not resticted to be and entity declaration in c
*)
wf_plays: "wf_ctxt c 
\<Longrightarrow> decl_of_kind c relt Relation
\<Longrightarrow> NamedTp rolet \<in> role_decls c
\<Longrightarrow> wf_ctxt ((Ctxt_plays_def (NamedTp et) (NamedTp relt) (NamedTp rolet)) # c)"
|
\<comment> \<open>Of the form:  \texttt{serial\_num value long}, also see \issueref{issue:decl_attribute} \<close>
wf_value: "wf_ctxt c 
\<Longrightarrow> decl_of_kind c at Attribute
\<Longrightarrow> wf_ctxt ((Ctxt_def (NamedTp at) Value (ValueTp vt)) # c )"

end
