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

#[derive(PartialEq, Eq, std::hash::Hash, Clone, Debug)]
enum Name {
  Atm(String),
  Num(u64),
  Par(u64)
} 

trait Get { fn get(FileBytes) -> Self; }

impl Get for char {
  fn get(bs: FileBytes) -> char { 
    char::from(bs.next().unwrap().unwrap())
  }
}

fn get_bytes(bs : FileBytes, mut v: Vec<u8>) -> Vec<u8> {
  let mut b = bs.next().unwrap().unwrap();
  while b != 36 {
    v.push(b);
    b = bs.next().unwrap().unwrap();
  }
  v
}

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

fn get_functor(bs: FileBytes) -> Functor {
  match char::get(bs) {
    '\'' => {
      let a = String::get(bs);
      Functor::Atm(a)
    },
    '@' => {
      let k = u64::get(bs);
      Functor::Par(k)
    },
    _ => panic!("Cannot parse functor")
  }
}

fn get_sign(bs: FileBytes) -> bool {
  match char::get(bs) {
    '+' => true,
    '-' => false,
    _ => panic!("Cannot parse sign")
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

impl Get for u64 {
  fn get(bs : FileBytes) -> u64 {
    let s = String::get(bs);
    s.parse::<u64>().unwrap()
  }
}

impl Get for Dir {
  fn get(bs: FileBytes) -> Dir { 
    match char::get(bs) {
      'l' => Dir::Lft,
      'r' => Dir::Rgt,
      _ => panic!("Cannot parse direction")
    }
  }
}

fn get_name(bs: FileBytes) -> Name { 
  match char::get(bs) {
    '\'' => {
      let a = String::get(bs);
      Name::Atm(a)
    }
    '@' => {
      let k = u64::get(bs);
      Name::Par(k)
    },
    '#' => {
      let k = u64::get(bs);
      Name::Num(k)
    },
    _ => panic!("Cannot parse name")
  }
}
// impl Get for Name {
//   fn get(bs: FileBytes) -> Name { 
//     match get_byte(bs) {
//       35 => Name::Num(u64::get(bs)),
//       b => {
//         let x = get_bytes(bs, vec![b]);
//         Name::Atm(str::from_utf8(&x).unwrap().to_string())
//       }
//     }
//   }
// }

impl Get for Term {
  fn get(bs : FileBytes) -> Term {
    match char::get(bs) {
      '#' => {
        let n = u64::get(bs);
        Term::Var(n)
      },
      '^' => {
        let f = get_functor(bs);
        let ts = get_vec::<Term>(bs); 
        Term::Fun(Rc::new(f), ts)
      },
      '"' => {
        let s = String::get(bs);
        Term::Dst(Rc::new(s))
      },
      _ => panic!("Cannot parse term")
    }
  }
}

impl Get for String {
  fn get(bs : FileBytes) -> String {
    let v = get_bytes(bs, vec![]);
    str::from_utf8(&v).unwrap().to_string() 
  }
}

impl Get for (String, Form) {
  fn get(bs : FileBytes) -> (String, Form) {
    let s = String::get(bs);
    let f = Form::get(bs);
    (s, f)
  }
}

impl Get for Form {

  fn get(bs : FileBytes) -> Form {
    match char::get(bs) {
      'T' => Form::True,
      'F' => Form::False,
      '~' => Form::Not(Rc::new(Form::get(bs))),
      '!' => Form::Fa(Rc::new(Form::get(bs))),
      '?' => Form::Ex(Rc::new(Form::get(bs))),
      '>' => {
        let f = Form::get(bs); 
        let g = Form::get(bs); 
        Form::Imp(Rc::new(f), Rc::new(g))
      },
      '&' => {
        let f = Form::get(bs); 
        let g = Form::get(bs); 
        return Form::And(Rc::new(f), Rc::new(g)); 
      },
      '|' => {
        let f = Form::get(bs); 
        let g = Form::get(bs); 
        return Form::Or(Rc::new(f), Rc::new(g)); 
      },
      '=' => {
        let f = Form::get(bs); 
        let g = Form::get(bs); 
        return Form::Iff(Rc::new(f), Rc::new(g)); 
      },
      '^' => {
        let f = get_functor(bs); 
        let ts: Vec<Term> = get_vec(bs); 
        return Form::Rel(Rc::new(f), ts); 
      },
      _ => panic!("Cannot parse formula")
    }
  }
}

fn mk_par_term(n: u64, ts: Vec<Term>) -> Term {
  Term::Fun(Rc::new(Functor::Par(n)), ts)
}

fn ab(d: Dir, x: &SignForm) -> SignForm {
  // let (s, f) = &*x;
  match (d, x.0, &*x.1) {
    (Dir::Lft, false, Form::Or(f,_))) => (false, f.clone()),
    (Dir::Rgt, false, Form::Or(_,f))) => (false, f.clone()),
    (Dir::Lft, true, Form::And(f,_)) => (true, f.clone()),
    (Dir::Rgt, true, Form::And(_,f)) => (true, f.clone()),
    (Dir::Lft, false, Form::Imp(f,_))) => (true, f.clone()),
    (Dir::Rgt, false, Form::Imp(_,f))) => (false, f.clone()),
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

fn get_vec<F: Get + std::fmt::Debug>(bs : FileBytes) -> Vec<F> {
  let mut c = char::get(bs); 
  let mut v = Vec::new();
  while c != '.' {
    assert!(c == ';');
    let x = F::get(bs);
    v.push(x);
    c = char::get(bs);
  };
  v
}

fn get_prob(bs : FileBytes) -> HashMap<Name, SignForm> {
  let mut c = char::get(bs); 
  let mut h = HashMap::new();
  while c != '.' {
    assert!(c == ';');
    let n = get_name(bs);
    let f = Form::get(bs);
    h.insert(n, (true, Rc::new(f)));
    c = char::get(bs);
  };
  h
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

fn get_prem<'a>(p: &'a HashMap<Name, SignForm>, n: &Name) -> &'a SignForm {
  match p.get(n) {
    Some(f) => f,
    None => panic!("No premise with name = {:?}", n)
  }
}

fn check(bs: FileBytes, mut prob: HashMap<Name, SignForm>, cnt: u64) -> Result<(), String> {
    
  //let cnm = mk_par_name(cnt); 
  let cnm = Name::Par(cnt);
  let succ = cnt + 1;

  match char::get(bs) {
    'A' => {
      let pnm = get_name(bs); 
      let d = Dir::get(bs); 
      let prem = get_prem(&prob,&pnm);
      let conc = ab(d,prem);
      prob.insert(cnm,conc);
      check(bs, prob, succ)
    },
    'B' => {
      let pnm = get_name(bs); 
      let prem = get_prem(&prob,&pnm);
      let (conc_l, conc_r) = bb(prem);
      let mut prob_alt = prob.clone();
      prob.insert(cnm.clone(), conc_l);
      prob_alt.insert(cnm, conc_r);
      check(bs, prob, succ).unwrap();
      check(bs, prob_alt, succ)
    },
    'C' => {
      let pnm = get_name(bs); 
      let trm = Term::get(bs); 
      let prem = get_prem(&prob,&pnm);
      if !ground_term(0, &trm) { 
        return Err("Instantiation term contains free variables.")
      };
      if !term_below(cnt, &trm) {
        return Err("Instantiation term contains OOB parameter.")
      }
      let conc = cb(trm,prem);
      prob.insert(cnm, conc);
      check(bs, prob, succ)
    },
    'D' => {
      let pnm = get_name(bs); 
      let prem = get_prem(&prob,&pnm);
      let conc = db(cnt,prem);
      prob.insert(cnm, conc);
      check(bs, prob, succ)
    },
    'F' => {
      let frm = Form::get(bs);
      assert!(ground_form(0, &frm), "Cut formula is not ground.");
      assert!(form_below(cnt, &frm), "Cut formula contains OOB parameter.");
      let x = Rc::new(frm);
      let mut prob_alt = prob.clone();
      prob.insert(cnm.clone(), (false, x.clone()));
      prob_alt.insert(cnm, (true, x));
      check(bs, prob, succ).unwrap();
      check(bs, prob_alt, succ)
    },
    'S' => {
      let pnm = get_name(bs); 
      let prem = get_prem(&prob,&pnm);
      let conc = sb(prem);
      prob.insert(cnm, conc);
      check(bs, prob, succ)
    },
    'T' => {
      let sgn = get_sign(bs);
      let frm = Form::get(bs);
      assert!(ground_form(0,&frm), "Cut formula is not ground.");
      assert!(form_below(cnt,&frm), "Cut formula contains OOB parameter.");
      assert!(justified(cnt,sgn,&frm), "Axiom introduction unjustified.");
      prob.insert(cnm, (sgn, Rc::new(frm)));
      check(bs, prob, succ)
    },
    'W' => {
      let pnm = get_name(bs); 
      match prob.remove(&pnm) {
        Some(_) => (),
        None => panic!("Deletion failed.")
      };
      check(bs, prob, succ)
    },
    'X' => { 
      let pnm = get_name(bs); 
      let nnm = get_name(bs); 
      match get_prem(&prob,&pnm) {
        (true,pfrm) => {
          match get_prem(&prob,&nnm) {
            (false,nfrm) => {
              assert_eq!(**pfrm, **nfrm, "Unequal positive and negative formulas.");
              Ok(())
            }
            _ => panic!("Second premise of X-rule not negative")
          }
        },
        _ => panic!("First premise of X-rule not positive")
      }
    },
    _ => panic!("Invalid head character of subproof.")
  }
}

fn main() -> io::Result<()> 
{
  let args: Vec<String> = env::args().collect();
  let tesc = &args[1];
  
  println!("Checking proof = {}", tesc);

  let f = BufReader::new(File::open("temp.ttp")?);
  let mut prob_bytes = f.bytes();
  let prob: HashMap<Name, SignForm> = get_prob(&mut prob_bytes);

  let size = prob.keys().len();
  println!("Problem size = {}", size);

  let g = BufReader::new(File::open(tesc)?);
  let mut proof_bytes = g.bytes();
  match check(&mut proof_bytes, prob, 0) {
    Ok(()) => println!("Proof verified."),
    _ => println!("Verification failed, invalid proof.")
  }
  Ok(())
}