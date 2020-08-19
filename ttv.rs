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
  Fun(Rc<String>, Vec<Term>),
  Dst(Rc<String>)
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
  Rel(Rc<String>, Vec<Term>)
} 

#[derive(PartialEq, Eq, std::hash::Hash, Clone, Debug)]
enum Name {
  Atm(String),
  Num(u64)
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
    Form::Rel(r,ts) => **r == "=".to_string() && *ts == vec![t, s],
    _ => false 
  }
}

fn pred_def(k: u64, f: &Form) -> bool {
  let (m,g) = strip_fas(f);
  match &**g {
    Form::Iff(h,i) => {

    }
    _ => false
  }
}

fn choice_axiom(k: u64, f: &Form) -> bool { unimplemented!() }

fn remove_fas(c: u64, f: &Form) -> (u64, &Form) {
  match f { 
    Form::Fa(g) => remove_fas(c+1,&*g),
    _ => (c, f)
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
  (b && choice_axiom(k,f)) ||
  (b && pred_def(k,f)) 
}

fn symb_below(k: u64, s: &String) -> bool {
  let mut cs = s.chars();
  match cs.next().unwrap() {
    '@' => {
      match cs.collect::<String>().parse::<u64>() {
        Ok(m) => m < k,
        _ => true
      }
    }
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
    Form::Not(g) => ground_form(k,f),
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

fn get_byte(bs : FileBytes) -> u8 {
  bs.next().unwrap().unwrap()
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

impl Get for Name {
  fn get(bs: FileBytes) -> Name { 
    match get_byte(bs) {
      35 => Name::Num(u64::get(bs)),
      b => {
        let x = get_bytes(bs, vec![b]);
        Name::Atm(str::from_utf8(&x).unwrap().to_string())
      }
    }
  }
}

impl Get for Term {
  fn get(bs : FileBytes) -> Term {
    match char::get(bs) {
      '#' => {
        let n = u64::get(bs);
        Term::Var(n)
      },
      '^' => {
        let s = String::get(bs);
        let ts = get_vec::<Term>(bs); 
        Term::Fun(Rc::new(s), ts)
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
      'T' => return Form::True,
      'F' => return Form::False,
      '~' => {
        let f = Form::get(bs); 
        return Form::Not(Rc::new(f)); 
      },
      '!' => {
        let f = Form::get(bs); 
        return Form::Fa(Rc::new(f)); 
      },
      '?' => {
        let f = Form::get(bs); 
        return Form::Ex(Rc::new(f)); 
      },
      '>' => {
        let f = Form::get(bs); 
        let g = Form::get(bs); 
        return Form::Imp(Rc::new(f), Rc::new(g)); 
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
        let s: String = String::get(bs); 
        let ts: Vec<Term> = get_vec(bs); 
        return Form::Rel(Rc::new(s), ts); 
      },
      _ => panic!("Cannot parse formula")
    }
  }
}

fn mk_par_term(n: u64) -> Term {
  Term::Fun(Rc::new(format!("{}{}", "@", n)), vec![])
}

fn mk_par_name(n: u64) -> Name {
  Name::Atm(format!("{}{}", "@", n))
}

fn ab(d: Dir, x: &SignForm) -> SignForm {
  // let (s, f) = &*x;
  match (d, x.0, &*x.1) {
    (Dir::Lft, true, Form::And(f,_)) => (true, f.clone()),
    (Dir::Lft, true, Form::Iff(f,g)) => (true, Rc::new(Form::Imp(f.clone(),g.clone()))),
    //(Dir::Lft, (false,Form::Or(f,_)))  => (false,**f),
    //(Dir::Lft, (false,Form::Imp(f,_))) => (true,**f),
   // 
   // (Dir::Rgt, (true,Form::And(_,f))) => (true,**f),
   // (Dir::Rgt, (false,Form::Or(_,f)))  => (false,**f),
   // (Dir::Rgt, (false,Form::Imp(_,f))) => (false,**f),
   // (Dir::Rgt, (true,Form::Iff(f,g))) => (true,Form::Imp(*g,*f)),
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
    (false,Form::Fa(g)) => (false,Rc::new(substform(0,&mk_par_term(n),&*g))),
    (true, Form::Ex(g)) => (true, Rc::new(substform(0,&mk_par_term(n),&*g))),
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
    let n = Name::get(bs);
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

fn substform(n: u64, t: &Term, f: &Form) -> Form {
  match f {
    Form::Not(g)   => Form::Not(Rc::new(substform(n,t,&*g))),
    Form::Or(g,h)  => Form::Or( Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::And(g,h) => Form::And(Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::Imp(g,h) => Form::Imp(Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::Iff(g,h) => Form::Iff(Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::Fa(g)    => Form::Fa(Rc::new(substform(n+1,t,&*g))),
    Form::Ex(g)    => Form::Ex(Rc::new(substform(n+1,t,&*g))),
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

fn check(bs: FileBytes, mut prob: HashMap<Name, SignForm>, cnt: u64) -> io::Result<()> {
    
  let cnm = mk_par_name(cnt); 
  let succ = cnt + 1;

  match char::get(bs) {
    'A' => {
      let pnm = Name::get(bs); 
      let d = Dir::get(bs); 
      let prem = get_prem(&prob,&pnm);
      let conc = ab(d,prem);
      prob.insert(cnm,conc);
      check(bs, prob, succ)
    },
    'B' => {
      let pnm = Name::get(bs); 
      let prem = get_prem(&prob,&pnm);
      let (conc_l, conc_r) = bb(prem);
      let mut prob_alt = prob.clone();
      prob.insert(cnm.clone(), conc_l);
      prob_alt.insert(cnm, conc_r);
      check(bs, prob, succ);
      check(bs, prob_alt, succ)
    },
    'C' => {
      let pnm = Name::get(bs); 
      let trm = Term::get(bs); 
      let prem = get_prem(&prob,&pnm);
      assert!(ground_term(0, &trm), "Instantiation term contains free variables.");
      assert!(term_below(cnt, &trm), "Instantiation term contains OOB parameter.");
      let conc = cb(trm,prem);
      prob.insert(cnm, conc);
      check(bs, prob, succ)
    },
    'D' => {
      let pnm = Name::get(bs); 
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
      check(bs, prob, succ);
      check(bs, prob_alt, succ)
    },
    'S' => {
      let pnm = Name::get(bs); 
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
      let pnm = Name::get(bs); 
      match prob.remove(&pnm) {
        Some(_) => (),
        None => panic!("Deletion failed.")
      };
      check(bs, prob, succ)
    },
    'X' => { 
      let pnm = Name::get(bs); 
      let nnm = Name::get(bs); 
      match get_prem(&prob,&pnm) {
        (true,pfrm) => {
          match get_prem(&prob,&pnm) {
            (false,nfrm) => {
              assert_eq!(**pfrm, **nfrm, "Unequal positive and negative formulas.");
              Ok(())
            }
            _ => panic!("Seconde premise of X-rule not negative")
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

  let f = BufReader::new(File::open("temp.ttp")?);
  let mut prob_bytes = f.bytes();
  let prob: HashMap<Name, SignForm> = get_prob(&mut prob_bytes);

  let size = prob.keys().len();
  println!("Problem size = {}", size);

  let g = BufReader::new(File::open(tesc)?);
  let mut proof_bytes = g.bytes();

  check(&mut proof_bytes, prob, 0)
}