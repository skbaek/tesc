use tptp::parsers::TPTPIterator;
use tptp::syntax::*;
use std::{str, env};
use std::io::prelude::*;
use std::fs::File;
use std::collections::HashMap;
use std::io::BufReader;
use std::rc::Rc;
use std::convert::TryFrom;

mod basic;
use basic::*;

const TPTPPATH: &str = "/home/sk/programs/TPTP/";

type SignForm = (bool, Rc<Form>);
type Problem = HashMap<ID, SignForm>;

fn mk_eq(t: Term, s: Term) -> Form { 
  Form::Rel(Rc::new(FS::Atm("=".to_string())), vec![t,s])
}
  
fn is_eq(t: Term, s: Term, f: &Form) -> bool { 
  match f {
    Form::Rel(g,ts) => {
      match &**g {
        FS::Atm(e) => {
          *e == "=".to_string() && *ts == vec![t, s]
        },
        _ => false
      }
    },
    _ => false 
  }
}

fn mk_vars_asc(k: u64) -> Vec<Term> {
  (0..k).map(|x| Term::Var(x)).collect()
}

fn mk_vars_desc(k: u64) -> Vec<Term> {
  (0..k).rev().map(|x| Term::Var(x)).collect()
}

fn is_vars(k: u64, ts: &Vec<Term>) -> bool {
  *ts == mk_vars_asc(k) || *ts == mk_vars_desc(k)
}

fn choice_axiom(k: u64, f: &Form) -> bool {
  match remove_fas(0,f) {
    (m, Form::Bct(Bct::Imp, f,g)) => {
      match &**f {
        Form::Qtf(Qtf::Ex, h) => {
          form_below(k,h) && 
          (
            substform(0, &mk_par_term(k, mk_vars_asc(m)), h) == **g ||
            substform(0, &mk_par_term(k, mk_vars_desc(m)), h) == **g 
          )
        },
        _ => false
      }
    },
    _ => false
  }
}

fn pred_def(k: u64, f: &Form) -> bool {
  let (m,g) = remove_fas(0,f);
  match g {
    Form::Bct(Bct::Iff,h,p) => {
      match &**h {
        Form::Rel(j, ts) => {
          match &**j {
            FS::Par(n) => {
              k == *n && 
              form_below(k, p) && 
              is_vars(m, ts) 
            },
            _ => false
          }
        },
        _ => false
      }
    }
    _ => false
  }
}

fn remove_fas(c: u64, f: &Form) -> (u64, &Form) {
  match f { 
    Form::Qtf(Qtf::Fa, g) => remove_fas(c+1,&*g),
    _ => (c, f)
  }
}

fn mono_args(k: u64) -> (Vec<Term>, Vec<Term>) {
  (
    (0..k).rev().map(|x| Term::Var((x*2)+1)).collect(), 
    (0..k).rev().map(|x| Term::Var(x*2)).collect()
  )
}
  
fn mono_body(k: u64, f: &Form) -> Option<(u64, &Form)> {
  match remove_fas(0, f) {
    (2, Form::Bct(Bct::Imp,g,h)) => {
      if is_eq(Term::Var(1), Term::Var(0), g) { mono_body(k+1, h) } 
      else { None }
    },
    (0, _) => Some((k,f)), 
    _ => None
  }
}

fn mono_fun(f: &Form) -> bool {
  match mono_body(0,f) {
    Some((k, Form::Rel(e,ts))) => {
      match &ts[..] {
        [Term::Fun(f0,ts0),Term::Fun(f1,ts1)] => {
          let (ss0,ss1) = mono_args(k);
          **e == FS::Atm("=".to_string()) && 
          *f0 == *f1 &&
          *ts0 == ss0 && *ts1 == ss1
        },
        _ => false
      }
    },
    _ => false
  }
}
    
fn mono_rel(f: &Form) -> bool {
  match mono_body(0,f) {
    Some((k, Form::Bct(Bct::Imp,g,h))) => {
      match (&**g,&**h) {
        (Form::Rel(ft0,ts0), Form::Rel(ft1,ts1)) => {
          let (ss0,ss1) = mono_args(k);
          *ft0 == *ft1 && *ts0 == ss0 && *ts1 == ss1
        },
        _ => false
      }
    },
    _ => false
  }
}

fn trans_axiom(f: &Form) -> bool {
  match remove_fas(0,f) {
    (3, Form::Bct(Bct::Imp, g,h)) => {
      is_eq(Term::Var(2), Term::Var(1), g) &&
      match &**h {
        Form::Bct(Bct::Imp, i,j) => 
          is_eq(Term::Var(1), Term::Var(0), i) &&
          is_eq(Term::Var(2), Term::Var(0), j),
        _ => false
      }
    },
    _ => false
  }
}

fn refl_axiom(f: &Form) -> bool {
  match f {
    Form::Qtf(Qtf::Fa, g) => is_eq(Term::Var(0), Term::Var(0), g),
    _ => false 
  }
}

fn symm_axiom(f: &Form) -> bool { 
  match f { 
    Form::Qtf(Qtf::Fa, g) => {
      match &**g {
        Form::Qtf(Qtf::Fa, h) => {
          match &**h {
            Form::Bct(Bct::Imp, i,j) => {
              is_eq(Term::Var(1), Term::Var(0), &*i) &&
              is_eq(Term::Var(0), Term::Var(1), &*j) 
            },
            _ => false
          }
        },
        _ => false
      }
    },
    _ => false 
  }
}

fn justified(k: u64, b: bool, f: &Form) -> bool {
  (b && *f == Form::Cst(true)) ||
  (!b && *f == Form::Cst(false)) ||
  (b && refl_axiom(f)) ||
  (b && symm_axiom(f)) ||
  (b && trans_axiom(f)) ||
  (b && mono_rel(f)) ||
  (b && mono_fun(f)) ||
  (b && choice_axiom(k,f)) ||
  (b && pred_def(k,f)) 
}

fn symb_below(k: u64, f: &FS) -> bool {
  match f {
    FS::Par(m) => *m < k,
    _ => true
  }
}

fn term_below(k: u64, t: &Term) -> bool {
  match t {
    Term::Fun(f,ts) => symb_below(k, &*f) && ts.iter().fold(true, |a, x| { a && term_below(k, x) }),
    _ => true
  }
}

fn ground_term(k: u64, t: &Term) -> bool {
  match t {
    Term::Var(m) => m < &k,
    Term::Fun(_,ts) => ts.iter().fold(true, |a, x| {a && ground_term(k, x)}),
    Term::Dst(_) => true,
    Term::Num(_) => true
  }
}

fn ground_form(k: u64, f: &Form) -> bool {
  match f {
    Form::Cst(_) => true,
    Form::Not(g) => ground_form(k,g),
    Form::Bct(_,g,h) => ground_form(k,g) && ground_form(k,h),
    Form::Qtf(_,g) => ground_form(k+1,g), 
    Form::Rel(_,ts) => ts.iter().fold(true, |a,x| { a && ground_term(k,x) })
  }
}

fn form_below(k: u64, f: &Form) -> bool {
  match f {
    Form::Cst(_) => true,
    Form::Not(g) => form_below(k,g),
    Form::Bct(_,g,h) => form_below(k,g) && form_below(k,h),
    Form::Qtf(_,g) => form_below(k,g),
    Form::Rel(_,ts) => ts.iter().fold(true, |a, x| { a && term_below(k,x) })
  }
}


fn mk_par_term(n: u64, ts: Vec<Term>) -> Term {
  Term::Fun(Rc::new(FS::Par(n)), ts)
}

fn ab(d: Dir, x: &SignForm) -> Rst<SignForm> {
  match (d, x.0, &*x.1) {
    (Dir::Lft, false, Form::Bct(Bct::Or, f,_))  => Ok((false, f.clone())),
    (Dir::Rgt, false, Form::Bct(Bct::Or, _,f))  => Ok((false, f.clone())),
    (Dir::Lft, true, Form::Bct(Bct::And, f,_))  => Ok((true, f.clone())),
    (Dir::Rgt, true, Form::Bct(Bct::And, _,f))  => Ok((true, f.clone())),
    (Dir::Lft, false, Form::Bct(Bct::Imp, f,_)) => Ok((true, f.clone())),
    (Dir::Rgt, false, Form::Bct(Bct::Imp, _,f)) => Ok((false, f.clone())),
    (Dir::Lft, true, Form::Bct(Bct::Iff, f,g))  => Ok((true, Rc::new(Form::Bct(Bct::Imp, f.clone(),g.clone())))),
    (Dir::Rgt, true, Form::Bct(Bct::Iff, f,g))  => Ok((true, Rc::new(Form::Bct(Bct::Imp, g.clone(),f.clone())))),
    _ => Err(format!("Not an A-formula : {:?}", x))
  }
}

fn bb(x: &SignForm) -> (SignForm, SignForm) {
  match (x.0,&*x.1) {
    (true,  Form::Bct(Bct::Or, f,g))  => ((true, f.clone()), (true, g.clone())),
    (false, Form::Bct(Bct::And, f,g)) => ((false,f.clone()), (false,g.clone())),
    (true,  Form::Bct(Bct::Imp, f,g)) => ((false,f.clone()), (true, g.clone())),
    (false, Form::Bct(Bct::Iff, f,g)) => ((false,Rc::new(Form::Bct(Bct::Imp, f.clone(),g.clone()))), (false,Rc::new(Form::Bct(Bct::Imp, g.clone(),f.clone())))),
    _ => panic!("Not a B-formula")
  }
}

fn cb(t: Term, x: &SignForm) -> SignForm {
  match (x.0,&*(x.1)) {
    (true,  Form::Qtf(Qtf::Fa, g)) =>(true, Rc::new(substform(0,&t,&*g))),
    (false, Form::Qtf(Qtf::Ex, g)) =>(false,Rc::new(substform(0,&t,&*g))),
    _ => panic!("Not a C-formula")
  }
}

fn db(n: u64, x: &SignForm) -> SignForm {
  match (x.0,&*x.1) {
    (false,Form::Qtf(Qtf::Fa, g)) => (false,Rc::new(substform(0,&mk_par_term(n,vec![]),&*g))),
    (true, Form::Qtf(Qtf::Ex, g)) => (true, Rc::new(substform(0,&mk_par_term(n,vec![]),&*g))),
    _ => panic!("Not a D-formula")
  }
}

fn sb(x: &SignForm) -> SignForm {
  match (x.0,&*x.1) {
    (false,Form::Not(g)) => (true, g.clone()),
    (true, Form::Not(g)) => (false,g.clone()),
    _ => panic!("Not an S-formula")
  }
}

/*
fn check_prob(pb: Problem, bs : FileBytes) -> Rst<()> {
  let mut c = get_char(bs)?; 
  while c != '.' {
    if c != ';' { return err_str("Ill-formed input problem.") };
    let n = get_id(bs)?;
    let f = get_form(bs)?;
     
    let g = match pb.get(&n) {
      Some((true, x)) => x,
      _ => return err_str("Premise not found")
    };

    if **g != f {
      return Err(format!("Hypothesis in problem = {:?}\nHypothesis expected = {:?}", g, f))
    } 
    c = get_char(bs)?;
  };
  Ok(())
}

fn get_prob(bs : FileBytes) -> Rst<Problem> {
  let mut c = get_char(bs)?; 
  let mut h = HashMap::new();
  while c != '.' {
    if c != ';' { return err_str("Ill-formed input problem.") };
    let n = get_id(bs)?;
    let f = get_form(bs)?;
    h.insert(n, (true, Rc::new(f)));
    c = get_char(bs)?;
  };
  Ok(h)
}
*/

fn substterm(k: u64, t: &Term, s: &Term) -> Term {
  match s {
    Term::Var(m) => {
      if k < *m { Term::Var(m-1) } 
      else if k == *m { t.clone() } 
      else { Term::Var(*m) }
    },
    Term::Fun(f,ts) => Term::Fun(f.clone(),ts.iter().map(|x| substterm(k,t,x)).collect()),
    Term::Dst(d) => Term::Dst(d.clone()),
    Term::Num(r) => Term::Num(r.clone())
  }
}

fn incrvarterm(t: &Term) -> Term {
  match t {
    Term::Var(m) => Term::Var(m+1), 
    Term::Fun(f,ts) => Term::Fun(f.clone(),ts.iter().map(|x| incrvarterm(x)).collect()),
    Term::Dst(d) => Term::Dst(d.clone()),
    Term::Num(s) => Term::Num(s.clone())
  }
}

fn substform(n: u64, t: &Term, f: &Form) -> Form {
  match f {
    Form::Cst(b) => Form::Cst(*b), 
    Form::Not(g) => Form::Not(Rc::new(substform(n,t,&*g))),
    Form::Bct(b,g,h)  => Form::Bct(*b, Rc::new(substform(n,t,&*g)), Rc::new(substform(n,t,&*h))),
    Form::Qtf(q,g)    => Form::Qtf(*q, Rc::new(substform(n+1,&incrvarterm(t),&*g))),
    Form::Rel(s,ts) => Form::Rel(s.clone(),ts.iter().map(|x| substterm(n,t,x)).collect()),
  }
}

fn get_prem<'a>(p: &'a Problem, n: &ID) -> Result<&'a SignForm, String> {
  match p.get(n) {
    Some(f) => Ok(f),
    None => Err(format!("No premise with name = {:?}", n))
  }
}

fn check(bs: FileBytes, mut prob: Problem) -> Result<(), String> {
    
  let mut cnm: ID;
  let mut cnt: u64 = 0;
  let mut probs: Vec<(Problem, u64)> = vec![];

  loop {

    cnm = ID::Par(cnt);

    match get_char(bs)? {
      'A' => {
        let pnm = get_id(bs)?; 
        let d = get_dir(bs)?;
        let prem = get_prem(&prob,&pnm)?;
        let conc = ab(d,prem)?;
        prob.insert(cnm,conc);
      },
      'B' => {
        let pnm = get_id(bs)?; 
        let prem = get_prem(&prob,&pnm)?;
        let (conc_l, conc_r) = bb(prem);
        let mut prob_alt = prob.clone();
        prob.insert(cnm.clone(), conc_l);
        prob_alt.insert(cnm, conc_r);
        probs.push((prob_alt, cnt));
      },
      'C' => {
        let pnm = get_id(bs)?; 
        let trm = get_term(bs)?; 
        let prem = get_prem(&prob,&pnm)?;
        if !ground_term(0, &trm) { return err_str("Instantiation term contains free variables.") };
        if !term_below(cnt, &trm) { return err_str("Instantiation term contains OOB parameter.") };
        let conc = cb(trm,prem);
        prob.insert(cnm, conc);
      },
      'D' => {
        let pnm = get_id(bs)?; 
        let prem = get_prem(&prob,&pnm)?;
        let conc = db(cnt,prem);
        prob.insert(cnm, conc);
      },
      'F' => {
        let frm = get_form(bs)?;
        if !ground_form(0, &frm)  { return err_str("Cut formula is not ground.") };
        if !form_below(cnt+1, &frm) { return err_str("Cut formula contains OOB parameter.") };
        let x = Rc::new(frm);
        let mut prob_alt = prob.clone();
        prob.insert(cnm.clone(), (false, x.clone()));
        prob_alt.insert(cnm, (true, x));
        probs.push((prob_alt, cnt));
      },
      'S' => {
        let pnm = get_id(bs)?; 
        let prem = get_prem(&prob,&pnm)?;
        let conc = sb(prem);
        prob.insert(cnm, conc);
      },
      'T' => {
        let sgn = get_sign(bs)?;
        let frm = get_form(bs)?;
        if !ground_form(0,&frm) { return err_str("Axiom is not ground.") };
        if !form_below(cnt+1,&frm) { return Err(format!("{:?} =< Parameter in axiom = {:?}", cnt, frm)) };
        if !justified(cnt,sgn,&frm) { return err_str("Axiom unjustified.") };
        prob.insert(cnm, (sgn, Rc::new(frm)));
      },
      'W' => {
        let pnm = get_id(bs)?; 
        match prob.remove(&pnm) {
          Some(_) => (),
          None => return err_str("Deletion failed.")
        };
      },
      'X' => { 
        let pnm = get_id(bs)?; 
        let nnm = get_id(bs)?; 
        match get_prem(&prob,&pnm)? {
          (true,pfrm) => {
            match get_prem(&prob,&nnm)? {
              (false,nfrm) => {
                if **pfrm == **nfrm { 
                  match probs.pop() {
                    Some((next_prob, next_cnt)) => {
                      prob = next_prob;
                      cnt = next_cnt;
                    },
                    None => return Ok(())
                  }
                }
                else { return Err(format!("Positive premise = {:?}\nNegative premise = {:?}", pfrm, nfrm)) }
              }
              _ => return err_str("Second premise of X-rule not negative.")
            }
          },
          _ => return err_str("First premise of X-rule not positive.")
        }
      },
      _ => return err_str("Invalid head character of subproof.")
    };

    cnt = cnt + 1;
  }
}

// TODO : Find out whether `'foo'` and `foo` should be considered distinct 
fn conv_atomic_word(a: AtomicWord) -> String {
  match a {
    AtomicWord::Lower(LowerWord(w)) => w.to_string(),
    AtomicWord::SingleQuoted(SingleQuoted(w)) => w.to_string()
  }
}

fn conv_name(n: Name) -> Rst<ID> {
  match n {
    // tptp::syntax::Name::AtomicWord(AtomicWord::Lower(LowerWord(w))) => Ok(ID::Atm((*w).to_string())),
    // tptp::syntax::Name::AtomicWord(AtomicWord::SingleQuoted(SingleQuoted(w))) => Ok(ID::Atm((*w).to_string())),
    Name::AtomicWord(a) => Ok(ID::Atm(conv_atomic_word(a))),
    Name::Integer(Integer(i)) => {
      match (*i).parse::<u64>() {
        Ok(k) => Ok(ID::Num(k)),
        _ => err_str("String cannot be parsed into u64")
      }
    }
  }
}

fn conjecturize(r: FormulaRole, f: Form) -> Form {
  match r {
    FormulaRole::Conjecture => Form::Not(Rc::new(f)),  
    _ => f
  }
}

fn conv_fof_unit_formula(vs: &mut Vec<String>, f: FofUnitFormula) -> Rst<Form> { 
  match f {
    FofUnitFormula::Unary(g) => conv_fof_unary_formula(vs,g),
    FofUnitFormula::Unitary(g) => conv_fof_unitary_formula(vs,g),
  }
}

fn chain_forms(b: Bct, fs: Vec<Form>) -> Rst<Form> {
  let mut i = fs.into_iter();
  let mut f: Form = match i.next() {
    Some(g) => g,
    _ => return err_str("Empty vector of forms")
  };
  for g in i { 
    f = Form::Bct(b,Rc::new(f),Rc::new(g)); 
  };
  Ok(f)
}

fn conv_vec_unit_formula(vs: &mut Vec<String>, b: Bct, fs: Vec<FofUnitFormula>) -> Rst<Form> {
  let sz = vs.len();
  let gs: Rst<Vec<Form>> = fs.into_iter().map(|x| {vs.truncate(sz); conv_fof_unit_formula(vs,x)}).collect();
  chain_forms(b,gs?)
}

fn find_variable_index(vs: &Vec<String>, v: Variable) -> Rst<u64> {
  let s = conv_variable(&v);
  let ei = vs.len() - 1;
  match vs.iter().position(|x| *x == s) {
    Some(i) => {
      match u64::try_from(ei-i) {
        Ok(x) => Ok(x),
        _ => err_str("Cannot convert usize to u64")
      }
    }, 
    _ => err_str("Unbound variable")
  }
}

fn conv_number(n: Number) -> String {
  match n {
    Number::Integer(Integer(s)) => s.to_string(),
    Number::Rational(Rational(s)) => s.to_string(),
    Number::Real(Real(s)) => s.to_string()
  }
}

fn conv_fof_term(vs: &Vec<String>, t: FofTerm) -> Rst<Term> {
  match t {
    FofTerm::Variable(v) => {
      let u = find_variable_index(vs, v)?;
      Ok(Term::Var(u))
    },
    FofTerm::Function(s) => {
      match *s {
        FofFunctionTerm::Defined(r) => {
          match r {
            FofDefinedTerm::Atomic(FofDefinedAtomicTerm(t)) => Ok(string_args_term(conv_fof_defined_plain_term(t),vec![])),
            FofDefinedTerm::Defined(q)=> {
              match q {
                DefinedTerm::Distinct(DistinctObject(p)) => Ok(Term::Dst(Rc::new((*p).to_string()))),
                DefinedTerm::Number(p) => Ok(Term::Num(Rc::new(conv_number(p))))
              }
            }
          }
        },
        FofFunctionTerm::Plain(r) => {
          let (fs,ts) = conv_fof_plain_term(vs, r)?;
          Ok(Term::Fun(Rc::new(fs),ts))
        } 
      }
    }
  }
}

fn conv_fof_infix_unary(vs: &Vec<String>, f: FofInfixUnary) -> Rst<Form> {
  match f {
    FofInfixUnary {left: l, op: _, right: r} => {
      let t = conv_fof_term(vs,*l)?;
      let s = conv_fof_term(vs,*r)?;
      Ok(Form::Not(Rc::new(mk_eq(t,s))))
    }
  }
}

fn conv_fof_unary_formula(vs: &mut Vec<String>, f: FofUnaryFormula) -> Rst<Form> {
  match f {
    FofUnaryFormula::Unary(_,g) => Ok(Form::Not(Rc::new(conv_fof_unit_formula(vs,*g)?))),
    FofUnaryFormula::InfixUnary(g) => conv_fof_infix_unary(vs,g)
  }
}

fn conv_fof_quantifier(q: FofQuantifier) -> Qtf {
  match q {
    FofQuantifier::Forall => Qtf::Fa,
    FofQuantifier::Exists => Qtf::Ex
  }
}

fn conv_variable(v: &Variable) -> String {
  match v { Variable {0: UpperWord {0: s}} => s.to_string() }
}

fn conv_functor(f: Functor) -> FS {
  match f { Functor(a) => FS::Atm(conv_atomic_word(a)) }
}
  
fn conv_fof_arguments(vs: &Vec<String>, f: FofArguments) -> Rst<Vec<Term>> {
  match f { FofArguments(g) => g.into_iter().map(|x| conv_fof_term(vs,x)).collect() }
}

fn conv_fof_plain_term(vs: &Vec<String>, f: FofPlainTerm) -> Rst<(FS,Vec<Term>)> {
  match f {
    FofPlainTerm::Constant(Constant(g)) => {
      Ok((conv_functor(g),vec![]))
    },
    FofPlainTerm::Function(g,h) => {
      Ok((conv_functor(g),conv_fof_arguments(vs,*h)?))
    }
  }
}

fn conv_fof_defined_plain_term(t: FofDefinedPlainTerm) -> String {
  match t {
    FofDefinedPlainTerm(
      DefinedConstant(
        DefinedFunctor(
          AtomicDefinedWord(
            DollarWord(
              LowerWord(s)
            )
          )
        )
      )
    ) => format!("${}",s)
  } 
}
  
fn conv_system_functor(f: SystemFunctor) -> String {
  match f {
    SystemFunctor(AtomicSystemWord(DollarDollarWord(LowerWord(s)))) =>
    format!("$${}",s)
  }
}


  
fn string_args_term(s: String, ts: Vec<Term>) -> Term {
  Term::Fun(Rc::new(FS::Atm(s)),ts)
}

fn string_args_form(s: String, ts: Vec<Term>) -> Form {
  Form::Rel(Rc::new(FS::Atm(s)),ts)
}

fn conv_fof_atomic_formula(vs: &Vec<String>, f: FofAtomicFormula) -> Rst<Form> {
  match f {
    FofAtomicFormula::Plain(g) => {
      match *g {
        FofPlainAtomicFormula {0: h} => {
          let (fs,ts) = conv_fof_plain_term(vs,h)?;
          Ok(Form::Rel(Rc::new(fs),ts))
        }
      }
    },
    FofAtomicFormula::Defined(g) => {
      match *g {
        FofDefinedAtomicFormula::Plain(FofDefinedPlainFormula(t)) => {
          let s = conv_fof_defined_plain_term(t);
          Ok(string_args_form(s,vec![]))
        },
        FofDefinedAtomicFormula::Infix(
          FofDefinedInfixFormula {left: l, op: _, right: r}
        ) => {
          let t = conv_fof_term(vs,*l)?;
          let s = conv_fof_term(vs,*r)?;
          Ok(mk_eq(t,s))
        }
      }
    },
    FofAtomicFormula::System(g) => {
      match *g {
        FofSystemAtomicFormula(h) => {
          match h {
            FofSystemTerm::Constant(SystemConstant(ft)) => {
              Ok(string_args_form(conv_system_functor(ft),vec![]))
            },
            FofSystemTerm::Function(i,j) => {
              Ok(string_args_form(conv_system_functor(i), conv_fof_arguments(vs,j)?))
            }
          }
        }
      }
    }
  }
}
  
fn apply_qtf(q: Qtf, f: Form) -> Form {
  Form::Qtf(q, Rc::new(f))
}

fn conv_fof_unitary_formula(vs: &mut Vec<String>, f: FofUnitaryFormula) -> Rst<Form> {
  match f {
    FofUnitaryFormula::Quantified(FofQuantifiedFormula {quantifier: q, bound: FofVariableList(l), formula: g}) => {
      let ss: Vec<String> = l.iter().map(|x| conv_variable(x)).collect();
      let lth = ss.len();
      vs.extend(ss);
      let mut h: Form = conv_fof_unit_formula(vs,*g)?;
      for _ in 0..lth { h = apply_qtf(conv_fof_quantifier(q),h); }
      Ok(h)
    },
    FofUnitaryFormula::Atomic(g) => conv_fof_atomic_formula(vs,g),
    FofUnitaryFormula::Parenthesised(g) => conv_fof_logic_formula(vs,*g)
  }
}

fn conv_fof_binary_assoc(vs: &mut Vec<String>, f: FofBinaryAssoc) -> Rst<Form> {
  match f {
    FofBinaryAssoc::Or(FofOrFormula {0: fs}) => conv_vec_unit_formula(vs,Bct::Or,fs),
    FofBinaryAssoc::And(FofAndFormula {0: fs}) => conv_vec_unit_formula(vs,Bct::And,fs)
  }
}
  
fn conv_fof_formula(vs: &mut Vec<String>, f: FofFormula) -> Rst<Form> {
  match f { FofFormula {0: g} => conv_fof_logic_formula(vs,g) }
}

fn apply_non_assoc_connective(c: NonassocConnective, f: Form, g: Form) -> Form {
  match c {
    NonassocConnective::Equivalent => Form::Bct(Bct::Iff,Rc::new(f),Rc::new(g)),
    NonassocConnective::LRImplies => Form::Bct(Bct::Imp,Rc::new(f),Rc::new(g)),
    NonassocConnective::RLImplies => Form::Bct(Bct::Imp,Rc::new(g),Rc::new(f)),
    NonassocConnective::NotOr => Form::Not(Rc::new(Form::Bct(Bct::Or,Rc::new(g),Rc::new(f)))),
    NonassocConnective::NotAnd => Form::Not(Rc::new(Form::Bct(Bct::And,Rc::new(g),Rc::new(f)))),
    NonassocConnective::NotEquivalent => Form::Not(Rc::new(Form::Bct(Bct::Iff,Rc::new(g),Rc::new(f))))
  }
}

fn conv_fof_logic_formula(vs: &mut Vec<String>, f: FofLogicFormula) -> Rst<Form> {
  match f {
    FofLogicFormula::Binary(FofBinaryFormula::Assoc(g)) => conv_fof_binary_assoc(vs,g),
    FofLogicFormula::Binary(FofBinaryFormula::Nonassoc(g)) => {
      match *g {
        FofBinaryNonassoc {left:lf,op:o,right:rf} => {
          let sz = vs.len();
          let nlf = conv_fof_unit_formula(vs,*lf)?;
          vs.truncate(sz);
          let nrf = conv_fof_unit_formula(vs,*rf)?;
          Ok(apply_non_assoc_connective(o,nlf,nrf))
        }
      }
    },
    FofLogicFormula::Unary(g) => conv_fof_unary_formula(vs,g),
    FofLogicFormula::Unitary(g) => conv_fof_unitary_formula(vs,g)
  }
}

fn vars_in_fof_arguments(vs: &mut Vec<String>, f: &FofArguments) -> () {
  match f { FofArguments(ts) => { for t in ts.iter() { vars_in_term(vs,t); } } }
}

fn vars_in_term(vs: &mut Vec<String>, t: &FofTerm) -> () {
  match t {
    FofTerm::Variable(v) => {
      let s = conv_variable(v);
      if !vs.contains(&s) { vs.push(s) }
    },
    FofTerm::Function(s) => {
      match &**s {
        FofFunctionTerm::Defined(_) => (),
        FofFunctionTerm::Plain(r) => vars_in_fof_plain_term(vs,r)
      }
    }
  }
}

fn vars_in_fof_atomic_formula(vs: &mut Vec<String>, f: &FofAtomicFormula) -> () {
  match f {
    FofAtomicFormula::System(g) => {
      match &**g {
        FofSystemAtomicFormula(h) => {
          match h {
            FofSystemTerm::Constant(_) => (),
            FofSystemTerm::Function(_,i) => vars_in_fof_arguments(vs,i)
          }
        }
      }
    }
    FofAtomicFormula::Defined(g) => {
      match &**g {
        FofDefinedAtomicFormula::Infix(h) => {
          match h {
            FofDefinedInfixFormula {left:lt, op: _, right: rt} => {
              vars_in_term(vs,&lt);
              vars_in_term(vs,&rt);
            }
          }
        },
        FofDefinedAtomicFormula::Plain(_) => ()
      }
    },
    FofAtomicFormula::Plain(g) => {
      match &**g { FofPlainAtomicFormula(h) => vars_in_fof_plain_term(vs,h) }
    }
  }
}

fn vars_in_fof_plain_term(vs: &mut Vec<String>, t: &FofPlainTerm) -> () {
  match t {
    FofPlainTerm::Constant(_) => (),
    FofPlainTerm::Function(_,i)=> vars_in_fof_arguments(vs,i)
  }
}

fn vars_in_literal(vs: &mut Vec<String>, l: &Literal) -> () {
  match l {
    Literal::Atomic(f) => vars_in_fof_atomic_formula(vs,f),
    Literal::NegatedAtomic(f) => vars_in_fof_atomic_formula(vs,f),
    Literal::Infix(FofInfixUnary {left: lt, op: _, right: rt}) => {
      vars_in_term(vs,&lt);
      vars_in_term(vs,&rt);
    }
  }
}

fn conv_literal(vs: &Vec<String>, l: Literal) -> Result<Form, String> {
  match l {
    Literal::Atomic(f) => conv_fof_atomic_formula(vs,f),
    Literal::NegatedAtomic(f) => Ok(Form::Not(Rc::new(conv_fof_atomic_formula(vs,f)?))),
    Literal::Infix(f) => conv_fof_infix_unary(vs,f) 
  }
}

fn conv_literals(ls: Vec<Literal>) -> Result<Form, String> {
  let mut vs: Vec<String> = vec![];
  for l in ls.iter() {
    vars_in_literal(&mut vs, l);
  }
  let k = vs.len();
  let fs: Rst<Vec<Form>> = ls.into_iter().map(|x| conv_literal(&vs,x)).collect();
  let mut f = chain_forms(Bct::Or, fs?)?;
  for _ in 0..k {
    f = Form::Qtf(Qtf::Fa,Rc::new(f));
  }
  Ok(f)
}

fn af_form(a: AnnotatedFormula) -> Result<(ID, Form), String> {
  match a {
    AnnotatedFormula::Fof(FofAnnotated {name: n, role: r, formula: f, annotations: _}) => {
      Ok((conv_name(*n)?, conjecturize(r, conv_fof_formula(&mut vec![],*f)?)))
    },
    AnnotatedFormula::Cnf(CnfAnnotated {name: n, role: r, formula: f, annotations: _}) => {
      match *f {
        CnfFormula::Disjunction(Disjunction(g))   => Ok((conv_name(*n)?, conjecturize(r, conv_literals(g)?))),
        CnfFormula::Parenthesised(Disjunction(g)) => Ok((conv_name(*n)?, conjecturize(r, conv_literals(g)?)))
      }
    }
  }
}

fn add_tptp_input(t: TPTPInput, pb: &mut Problem) -> Rst<()> {
  match t {
    TPTPInput::Annotated(a) => {
      let (n,f) = af_form(a)?;
      println!("Adding original formula = {:?} : {:?}", n, f);
      if !ground_form(0, &f) { return err_str("Added formula is not ground.") };
      match pb.insert(n, (true, Rc::new(f))) {
        Some(_) => err_str("Duplicate name found"),
        None => {
          Ok(())
        }
      }
    },
    TPTPInput::Include(Include {file_name: FileName(SingleQuoted(s)), selection: _}) => {
      let pt: String = format!("{}{}", TPTPPATH, s);
      add_tptp_file(&pt, pb)
    }
  }
}

fn add_tptp_file(tptp: &str, p: &mut Problem) -> Rst<()> {
    
   let bytes = to_boxed_slice(tptp)?;
   let mut is = TPTPIterator::<()>::new(&bytes);
   // let mut h = HashMap::new();

   for x in &mut is {
     //println!("{}", x.expect("syntax error"));
     match x {
       Ok(i) => add_tptp_input(i,p)?,
       _ => return err_str("Invalid item from TPTP problem file")
     }
   }
   assert!(is.remaining.is_empty());
   Ok(())
}


fn main() -> Rst<()> {
  let args: Vec<String> = env::args().collect();
  let tptp = &args[1];
  let tesc = &args[2];
  // let ttp = &args[2];
  
  println!("Checking problem = {}", tptp);
  println!("Checking proof = {}", tesc);
  
  // let pbf = match File::open("temp.ttp") {
  //   Ok(file) => BufReader::new(file),
  //   _ => return err_str("Cannot open TTP file.")
  // };
  // let mut pbbs = pbf.bytes();
  
  let mut pb = HashMap::new();
  add_tptp_file(tptp, &mut pb)?;

  let size = pb.keys().len();
  println!("Problem size = {}", size);

  let prf = match File::open(tesc) {
    Ok(tesc_file) => BufReader::new(tesc_file), 
    _ => return err_str("Cannot open TESC file.")
  };
  let mut prbs = prf.bytes();

  println!("\n\n\n------Begin proofcheck------\n\n\n");
  
  match check(&mut prbs, pb) {
    Ok(()) => println!("Proof verified"),
    Err(msg) => println!("Invalid proof : {:?}", msg)
  };

  Ok(())
}
