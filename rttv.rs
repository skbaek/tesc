// use std::env;
use std::io;
use std::env;
use std::str;
use std::io::prelude::*;
use std::fs::File;
use std::collections::HashMap;
use std::io::BufReader;
use std::rc::Rc;

type FileBytes<'a> = &'a mut io::Bytes<io::BufReader<File>>;
type SignForm = (bool, Rc<Form>);
type Problem = HashMap<Name, SignForm>;

#[derive(Debug)]
enum Dir {Lft, Rgt}

#[derive(PartialEq, Clone, Debug)]
enum Term {
  Var(u64),
  Fun(Rc<Functor>, Vec<Term>),
  Dst(Rc<String>)
}

#[derive(PartialEq, Clone, Debug)]
enum Functor {
  Par(u64),
  Atm(String),
}

#[derive(PartialEq, Clone, Debug)]
enum Form {
  True, 
  False,
  Not(Rc<Form>),
  Fa( Rc<Form>),
  Ex( Rc<Form>),
  And(Rc<Form>, Rc<Form>),
  Or( Rc<Form>, Rc<Form>),
  Imp(Rc<Form>, Rc<Form>),
  Iff(Rc<Form>, Rc<Form>),
  Rel(Rc<Functor>, Vec<Term>)
} 

enum FormPart {
  True, 
  False,
  Not,
  Fa,
  Ex,
  And,
  Or,
  Imp,
  Iff,
  Rel(Rc<Functor>, Vec<Term>)
} 

#[derive(PartialEq, Eq, std::hash::Hash, Clone, Debug)]
enum Name {
  Atm(String),
  Num(u64),
  Par(u64)
} 

trait Get { fn get(FileBytes) -> Result<Self, String> where Self: std::marker::Sized; }

fn err_str<T>(s: &str) -> Result<T, String> { 
  Err(s.to_string())
}

fn get_char(bs: FileBytes) -> Result<char, String> { 
  let c = char::from(get_byte(bs)?);
  // print!("{}", c);
  Ok(c)
}

fn get_byte(bs : FileBytes) -> Result<u8, String> {
  match bs.next() {
    Some(x) => match x {
      Ok(b) => Ok(b),
      _ => err_str("Cannot read next byte")
    },
    None => err_str("Cannot read next byte")
  }
}

// fn get_bytes(bs : FileBytes) -> Result<Vec<u8>, String> {
//   let mut v: Vec<u8> = vec![];
//   let mut b = get_byte(bs)?;
//   while b != 36 {
//     v.push(b);
//     b = get_byte(bs)?;
//   }
//   Ok(v)
// }

fn is_eq(t: Term, s: Term, f: &Form) -> bool { 
  match f {
    Form::Rel(g,ts) => {
      match &**g {
        Functor::Atm(e) => {
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

// fn is_vars_desc(k: u64, ts: &Vec<Term>) -> bool {
//   let mut x: u64 = k;
//   for t in ts {
//     match t {
//       Term::Var(m) => {
//         if *m == (x-1) && 0 < x {
//           x = x - 1;
//         } else { 
//           return false;
//         }
//       },
//       _ => return false
//     }
//   };
//   x == 0
// }
// 
// fn is_vars_asc(k: u64, ts: &Vec<Term>) -> bool {
//   let mut x: u64 = 0;
//   for t in ts {
//     match t {
//       Term::Var(m) => {
//         if *m == x && x < k {
//           x = x + 1;
//         } else { 
//           return false;
//         }
//       },
//       _ => return false
//     }
//   };
//   x == k
// }

fn is_vars(k: u64, ts: &Vec<Term>) -> bool {
  *ts == mk_vars_asc(k) || *ts == mk_vars_desc(k)
}

fn choice_axiom(k: u64, f: &Form) -> bool {
  match remove_fas(0,f) {
    (m, Form::Imp(f,g)) => {
      match &**f {
        Form::Ex(h) => {
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
    Form::Iff(h,p) => {
      match &**h {
        Form::Rel(j, ts) => {
          match &**j {
            Functor::Par(n) => {
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
    Form::Fa(g) => remove_fas(c+1,&*g),
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
    (2, Form::Imp(g,h)) => {
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
          **e == Functor::Atm("=".to_string()) && 
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
    Some((k, Form::Imp(g,h))) => {
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
    (3, Form::Imp(g,h)) => {
      is_eq(Term::Var(2), Term::Var(1), g) &&
      match &**h {
        Form::Imp(i,j) => 
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
    Form::Fa(g) => is_eq(Term::Var(0), Term::Var(0), g),
    _ => false 
  }
}

fn symm_axiom(f: &Form) -> bool { 
  match f { 
    Form::Fa(g) => {
      match &**g {
        Form::Fa(h) => {
          match &**h {
            Form::Imp(i,j) => {
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
  (b && *f == Form::True) ||
  (!b && *f == Form::False) ||
  (b && refl_axiom(f)) ||
  (b && symm_axiom(f)) ||
  (b && trans_axiom(f)) ||
  (b && mono_rel(f)) ||
  (b && mono_fun(f)) ||
  (b && choice_axiom(k,f)) ||
  (b && pred_def(k,f)) 
}

fn symb_below(k: u64, f: &Functor) -> bool {
  match f {
    Functor::Par(m) => *m < k,
    _ => true
  }
}

fn term_below(k: u64, t: &Term) -> bool {
  match t {
    Term::Dst(_) => true,
    Term::Var(_) => true,
    Term::Fun(f,ts) => 
      symb_below(k, &*f) && ts.iter().fold(true, |a, x| { a && term_below(k, x) })
  }
}

fn ground_term(k: u64, t: &Term) -> bool {
  match t {
    Term::Dst(_) => true,
    Term::Var(m) => m < &k,
    Term::Fun(_,ts) => ts.iter().fold(true, |a, x| { a && ground_term(k, x) } )
  }
}


fn get_functor(bs: FileBytes) -> Result<Functor, String> {
  match get_char(bs)? {
    '\'' => {
      let a = get_string(bs)?;
      Ok(Functor::Atm(a))
    },
    '@' => {
      let k = get_u64(bs)?;
      Ok(Functor::Par(k))
    },
    _ => err_str("Cannot parse functor")
  }
}

fn get_sign(bs: FileBytes) -> Result<bool, String> {
  match get_char(bs)? {
    '+' => Ok(true),
    '-' => Ok(false),
    _ => err_str("Cannot parse sign")
  }
}

fn ground_form(k: u64, f: &Form) -> bool {
  match f {
    Form::True => true,
    Form::False => true,
    Form::Not(g) => ground_form(k,g),
    Form::Or(g,h) => ground_form(k,g) && ground_form(k,h),
    Form::And(g,h) => ground_form(k,g) && ground_form(k,h),
    Form::Imp(g,h) => ground_form(k,g) && ground_form(k,h),
    Form::Iff(g,h) => ground_form(k,g) && ground_form(k,h),
    Form::Fa(g) => ground_form(k+1,g), 
    Form::Ex(g) => ground_form(k+1,g), 
    Form::Rel(_,ts) => ts.iter().fold(true, |a,x| { a && ground_term(k,x) })
  }
}

fn form_below(k: u64, f: &Form) -> bool {
  match f {
    Form::True => true,
    Form::False => true,
    Form::Not(g) => form_below(k,g),
    Form::Or(g,h) => form_below(k,g) && form_below(k,h),
    Form::And(g,h) => form_below(k,g) && form_below(k,h),
    Form::Imp(g,h) => form_below(k,g) && form_below(k,h),
    Form::Iff(g,h) => form_below(k,g) && form_below(k,h),
    Form::Fa(g) => form_below(k,g),
    Form::Ex(g) => form_below(k,g),
    Form::Rel(_,ts) => ts.iter().fold(true, |a, x| { a && term_below(k,x) })
  }
}

fn get_u64(bs : FileBytes) -> Result<u64, String> {
  let s = get_string(bs)?;
  match s.parse::<u64>() {
    Ok(k) => Ok(k),
    _ => err_str("Cannot parse String to u64")
  }
}

fn get_dir(bs: FileBytes) -> Result<Dir, String> { 
  match get_char(bs)? {
    '<' => Ok(Dir::Lft),
    '>' => Ok(Dir::Rgt),
     c  => Err(format!("Cannot parse direction from char = {}", c))
  }
}

fn get_name(bs: FileBytes) -> Result<Name, String> { 
  match get_char(bs)? {
    '\'' => {
      let a = get_string(bs)?;
      Ok(Name::Atm(a))
    }
    '@' => {
      let k = get_u64(bs)?;
      Ok(Name::Par(k))
    },
    '#' => {
      let k = get_u64(bs)?;
      Ok(Name::Num(k))
    },
    _ => err_str("Cannot parse name")
  }
}

fn get_term(bs : FileBytes) -> Result<Term, String> {
  match get_char(bs)? {
    '#' => {
      let n = get_u64(bs)?;
      Ok(Term::Var(n))
    },
    '^' => {
      let f = get_functor(bs)?;
      let ts = get_vec::<Term>(bs)?; 
      Ok(Term::Fun(Rc::new(f), ts))
    },
    '"' => {
      let s = get_string(bs)?;
      Ok(Term::Dst(Rc::new(s)))
    },
    _ => err_str("Cannot parse term")
  }
}

impl Get for Term {
  fn get(bs: FileBytes) -> Result<Term, String> { get_term(bs) }
}

fn get_string(bs : FileBytes) -> Result<String, String> {
  let mut c = get_char(bs)?;
  let mut s = String::from("");
  while c != '$' {
    s.push(c);
    c = get_char(bs)?;
  }
  Ok(s)
}

// fn get_string(bs : FileBytes) -> Result<String, String> {
//   let v = get_bytes(bs)?;
//   match str::from_utf8(&v) {
//     Ok(s) => Ok(s.to_string()),
//     _ => err_str("Cannot convert Vec<u8> to &str")
//   }
// }

fn build_form(mut ps: Vec<FormPart>) -> Option<Form> {
  let mut fs: Vec<Form> = vec![];
  loop {
    match ps.pop() {
      Some(p) => {
        match p {
          FormPart::True => fs.push(Form::True),
          FormPart::False => fs.push(Form::False),
          FormPart::Not => {
            let f = fs.pop()?;
            fs.push(Form::Not(Rc::new(f)));
          },
          FormPart::Or => {
            let f = fs.pop()?;
            let g = fs.pop()?;
            fs.push(Form::Or(Rc::new(f),Rc::new(g)));
          },
          FormPart::And => {
            let f = fs.pop()?;
            let g = fs.pop()?;
            fs.push(Form::And(Rc::new(f),Rc::new(g)));
          },
          FormPart::Imp => {
            let f = fs.pop()?;
            let g = fs.pop()?;
            fs.push(Form::Imp(Rc::new(f),Rc::new(g)));
          },
          FormPart::Iff => {
            let f = fs.pop()?;
            let g = fs.pop()?;
            fs.push(Form::Iff(Rc::new(f),Rc::new(g)));
          },
          FormPart::Fa => {
            let f = fs.pop()?;
            fs.push(Form::Fa(Rc::new(f)));
          },
          FormPart::Ex => {
            let f = fs.pop()?;
            fs.push(Form::Ex(Rc::new(f)));
          },
          FormPart::Rel(ft,ts) => fs.push(Form::Rel(ft,ts))
        }
      },
      None => {
        if fs.len() == 1 { return Some(fs.pop()?) }
        else { return None }
      }
    }
  }
}

fn get_form(bs: FileBytes) -> Result<Form, String> {
  let mut rem: u64 = 1;
  let mut stk: Vec<FormPart> = vec![];
  while 0 < rem {
    match get_char(bs)? {
      'T' => {
         stk.push(FormPart::True);
         rem = rem - 1; 
      }, 
      'F' => {
         stk.push(FormPart::False);
         rem = rem - 1; 
      }, 
      '~' => stk.push(FormPart::Not),
      '!' => stk.push(FormPart::Fa),
      '?' => stk.push(FormPart::Ex),
      '|' => {
         stk.push(FormPart::Or);
         rem = rem + 1; 
      },
      '&' => {
         stk.push(FormPart::And);
         rem = rem + 1; 
      },
      '>' => {
         stk.push(FormPart::Imp);
         rem = rem + 1; 
      },
      '=' => {
         stk.push(FormPart::Iff);
         rem = rem + 1; 
      },
      '^' => {
        let f = get_functor(bs)?; 
        let ts: Vec<Term> = get_vec(bs)?; 
        stk.push(FormPart::Rel(Rc::new(f), ts));
        rem = rem - 1; 
      },
      _ => return err_str("Ill-formed formula")
    }
  };
  match build_form(stk) {
    Some(f) => Ok(f),
    _ => err_str("Cannot build formula from parts stack.")
  }
}

/*
fn get_form(bs : FileBytes) -> Result<Form, String> {
  match get_char(bs)? {
    'T' => Ok(Form::True),
    'F' => Ok(Form::False),
    '~' => Ok(Form::Not(Rc::new(get_form(bs)?))),
    '!' => Ok(Form::Fa(Rc::new(get_form(bs)?))),
    '?' => Ok(Form::Ex(Rc::new(get_form(bs)?))),
    '>' => {
      let f = get_form(bs)?; 
      let g = get_form(bs)?; 
      Ok(Form::Imp(Rc::new(f), Rc::new(g)))
    },
    '&' => {
      let f = get_form(bs)?; 
      let g = get_form(bs)?; 
      Ok(Form::And(Rc::new(f), Rc::new(g)))
    },
    '|' => {
      let f = get_form(bs)?; 
      let g = get_form(bs)?; 
      Ok(Form::Or(Rc::new(f), Rc::new(g))) 
    },
    '=' => {
      let f = get_form(bs)?; 
      let g = get_form(bs)?; 
      Ok(Form::Iff(Rc::new(f), Rc::new(g)))
    },
    '^' => {
      let f = get_functor(bs)?; 
      let ts: Vec<Term> = get_vec(bs)?; 
      Ok(Form::Rel(Rc::new(f), ts)) 
    },
    _ => err_str("Cannot get formula")
  }
}
*/

fn mk_par_term(n: u64, ts: Vec<Term>) -> Term {
  Term::Fun(Rc::new(Functor::Par(n)), ts)
}

fn ab(d: Dir, x: &SignForm) -> SignForm {
  match (d, x.0, &*x.1) {
    (Dir::Lft, false, Form::Or(f,_)) => (false, f.clone()),
    (Dir::Rgt, false, Form::Or(_,f)) => (false, f.clone()),
    (Dir::Lft, true, Form::And(f,_)) => (true, f.clone()),
    (Dir::Rgt, true, Form::And(_,f)) => (true, f.clone()),
    (Dir::Lft, false, Form::Imp(f,_)) => (true, f.clone()),
    (Dir::Rgt, false, Form::Imp(_,f)) => (false, f.clone()),
    (Dir::Lft, true, Form::Iff(f,g)) => (true, Rc::new(Form::Imp(f.clone(),g.clone()))),
    (Dir::Rgt, true, Form::Iff(f,g)) => (true, Rc::new(Form::Imp(g.clone(),f.clone()))),
    _ => panic!("Not an A-formula")
  }
}

fn bb(x: &SignForm) -> (SignForm, SignForm) {
  match (x.0,&*x.1) {
    (true,  Form::Or(f,g))  => ((true, f.clone()), (true, g.clone())),
    (false, Form::And(f,g)) => ((false,f.clone()), (false,g.clone())),
    (true,  Form::Imp(f,g)) => ((false,f.clone()), (true, g.clone())),
    (false, Form::Iff(f,g)) => ((false,Rc::new(Form::Imp(f.clone(),g.clone()))), (true,Rc::new(Form::Imp(g.clone(),f.clone())))),
    _ => panic!("Not a B-formula")
  }
}

fn cb(t: Term, x: &SignForm) -> SignForm {
  match (x.0,&*(x.1)) {
    (true,  Form::Fa(g)) =>(true, Rc::new(substform(0,&t,&*g))),
    (false, Form::Ex(g)) =>(false,Rc::new(substform(0,&t,&*g))),
    _ => panic!("Not a C-formula")
  }
}

fn db(n: u64, x: &SignForm) -> SignForm {
  match (x.0,&*x.1) {
    (false,Form::Fa(g)) => (false,Rc::new(substform(0,&mk_par_term(n,vec![]),&*g))),
    (true, Form::Ex(g)) => (true, Rc::new(substform(0,&mk_par_term(n,vec![]),&*g))),
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

fn get_vec<F: Get>(bs : FileBytes) -> Result<Vec<F>, String> {
  let mut c = get_char(bs)?; 
  let mut v = vec![];
  while c != '.' {
    if c != ';' { return err_str("Cannot get vector.") };
    let x = F::get(bs)?;
    v.push(x);
    c = get_char(bs)?;
  };
  Ok(v)
}

fn get_prob(bs : FileBytes) -> Result<Problem, String> {
  let mut c = get_char(bs)?; 
  let mut h = HashMap::new();
  while c != '.' {
    if c != ';' { return err_str("Ill-formed input problem.") };
    let n = get_name(bs)?;
    let f = get_form(bs)?;
    h.insert(n, (true, Rc::new(f)));
    c = get_char(bs)?;
  };
  Ok(h)
}

fn substterm(k: u64, t: &Term, s: &Term) -> Term {
  match s {
    Term::Var(m) => {
      if k < *m { Term::Var(m-1) } 
      else if k == *m { t.clone() } 
      else { Term::Var(*m) }
    },
    Term::Fun(f,ts) => Term::Fun(f.clone(),ts.iter().map(|x| substterm(k,t,x)).collect()),
    Term::Dst(d) => Term::Dst(d.clone())
  }
}

fn incrvarterm(t: &Term) -> Term {
  match t {
    Term::Var(m) => Term::Var(m+1), 
    Term::Fun(f,ts) => Term::Fun(f.clone(),ts.iter().map(|x| incrvarterm(x)).collect()),
    Term::Dst(d) => Term::Dst(d.clone())
  }
}

fn substform(n: u64, t: &Term, f: &Form) -> Form {
  match f {
    Form::Not(g)   => Form::Not(Rc::new(substform(n,t,&*g))),
    Form::Or(g,h)  => Form::Or( Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::And(g,h) => Form::And(Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::Imp(g,h) => Form::Imp(Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::Iff(g,h) => Form::Iff(Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::Fa(g)    => Form::Fa(Rc::new(substform(n+1,&incrvarterm(t),&*g))),
    Form::Ex(g)    => Form::Ex(Rc::new(substform(n+1,&incrvarterm(t),&*g))),
    Form::Rel(s,ts) => Form::Rel(s.clone(),ts.iter().map(|x| substterm(n,t,x)).collect()),
    Form::True => Form::True,
    Form::False => Form::False
  }
}

fn get_prem<'a>(p: &'a Problem, n: &Name) -> Result<&'a SignForm, String> {
  match p.get(n) {
    Some(f) => Ok(f),
    None => Err(format!("No premise with name = {:?}", n))
  }
}

fn check(bs: FileBytes, mut prob: Problem) -> Result<(), String> {
    
  let mut cnm: Name;
  let mut cnt: u64 = 0;
  let mut probs: Vec<(Problem, u64)> = vec![];

  loop {

    cnm = Name::Par(cnt);

    match get_char(bs)? {
      'A' => {
        let pnm = get_name(bs)?; 
        let d = get_dir(bs)?;
        let prem = get_prem(&prob,&pnm)?;
        let conc = ab(d,prem);
        prob.insert(cnm,conc);
      },
      'B' => {
        let pnm = get_name(bs)?; 
        let prem = get_prem(&prob,&pnm)?;
        let (conc_l, conc_r) = bb(prem);
        let mut prob_alt = prob.clone();
        prob.insert(cnm.clone(), conc_l);
        prob_alt.insert(cnm, conc_r);
        probs.push((prob_alt, cnt));
      },
      'C' => {
        let pnm = get_name(bs)?; 
        let trm = get_term(bs)?; 
        let prem = get_prem(&prob,&pnm)?;
        if !ground_term(0, &trm) { return err_str("Instantiation term contains free variables.") };
        if !term_below(cnt, &trm) { return err_str("Instantiation term contains OOB parameter.") };
        let conc = cb(trm,prem);
        prob.insert(cnm, conc);
      },
      'D' => {
        let pnm = get_name(bs)?; 
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
        let pnm = get_name(bs)?; 
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
        let pnm = get_name(bs)?; 
        match prob.remove(&pnm) {
          Some(_) => (),
          None => return err_str("Deletion failed.")
        };
      },
      'X' => { 
        let pnm = get_name(bs)?; 
        let nnm = get_name(bs)?; 
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
                else { return err_str("Unequal positive and negative formulas.") }
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

fn body() -> Result<(), String> {
  let args: Vec<String> = env::args().collect();
  let tesc = &args[1];
  
  println!("Checking proof = {}", tesc);
  let pbf = match File::open("temp.ttp") {
    Ok(file) => BufReader::new(file),
    _ => return err_str("Cannot open TTP file.")
  };
  let mut pbbs = pbf.bytes();
  let pb: Problem = get_prob(&mut pbbs)?;

  let size = pb.keys().len();
  println!("Problem size = {}", size);

  let prf = match File::open(tesc) {
    Ok(tesc_file) => BufReader::new(tesc_file), 
    _ => return err_str("Cannot open TESC file.")
  };
  let mut prbs = prf.bytes();

  println!("\n\n\n-----Begin proofcheck here!!------\n\n\n");
  check(&mut prbs, pb) 
}
 
fn main() {
  std::process::exit(
    match body() {
      Ok(()) => {
        println!("Proof verified.");
        0
      },
      Err(msg) => {
        println!("Invalid proof : {:?}", msg);
        1
      }
    }
  );
}