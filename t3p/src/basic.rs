use std::rc::Rc;
use std::env;
use std::io::{BufReader, BufWriter};
use std::fs::File;
use std::io;
use std::io::{Read, Write};
use tptp::*;
use tptp::top::*;
use tptp::common::*;
use std::convert::TryFrom;

pub type Rst<T> = std::result::Result<T, String>;
pub type ReadBytes = io::Bytes<io::BufReader<File>>;
pub type WriteBytes = io::BufWriter<File>;
pub type ReadBytesRef<'a> = &'a mut ReadBytes;
pub type WriteBytesRef<'a> = &'a mut WriteBytes;

pub fn get_read_bytes(file_name: &str, err_msg: &str) -> ReadBytes {
  BufReader::new(File::open(file_name).expect(err_msg)).bytes()
}


pub fn get_write_bytes(file_name: &str, err_msg: &str) -> WriteBytes {
  BufWriter::new(File::create(file_name).expect("Cannot create TESC file"))
}

trait Get { fn get(_: ReadBytesRef) -> Rst<Self> where Self: std::marker::Sized; }
pub trait Put { fn put<W: Write>(_: &mut W, _: &Self) -> Rst<()> where Self: std::marker::Sized; }
trait Conv<T> { fn conv(_: Self) -> Rst<T>; }

struct Terms<'a>(&'a Vec<Term>);

#[derive(PartialEq, Clone, Debug)]
pub enum FS {
  Par(u64),
  Atm(String),
}

#[derive(PartialEq, Clone, Debug)]
pub enum Term {
  Var(u64),
  Fun(Rc<FS>, Vec<Term>),
}

pub enum GT {
  Fun(String, Vec<GT>),
  List(Vec<GT>)
}

#[derive(PartialEq, Clone, Debug, Copy)]
pub enum Bct {Or, And, Imp, Iff}

#[derive(PartialEq, Clone, Debug)]
pub enum Form {
  Cst(bool),
  Not(Rc<Form>),
  Bct(Bct, Rc<Form>, Rc<Form>),
  Qtf(bool, Rc<Form>),
  Rel(Rc<FS>, Vec<Term>)
} 


impl std::fmt::Display for Bct {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match *self {
      Bct::Or => write!(f,"∨"),
      Bct::And => write!(f,"∧"),
      Bct::Imp => write!(f,"→"),
      Bct::Iff => write!(f,"↔")
    }
  }
}

 impl std::fmt::Display for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Term::Var(k) => write!(f, "#{}", k),
      Term::Fun(g,ts) => write!(f, "{}{}", g, Terms(ts))
    }
  }
}

impl<'a> std::fmt::Display for Terms<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    let i = self.0.iter();
    let mut trailing: bool = false;
    write!(f, "(")?;
    for x in i {
      if trailing { write!(f, ",")?; };
      write!(f, "{}", x)?;
      trailing = true;
    };
    write!(f, ")")
  }
}

 impl std::fmt::Display for FS {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      FS::Par(n) => write!(f, "#{}", n), 
      FS::Atm(s) => write!(f, "{}", s) 
    }
  }
}

impl std::fmt::Display for Form {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Form::Cst(true)  => write!(f, "⊤"),
      Form::Cst(false) => write!(f, "⊥"),
      Form::Not(g) => write!(f, "¬ {}", g),
      Form::Bct(b,g,h) => write!(f, "({} {} {})", g, b, h),
      Form::Qtf(true,g)  => write!(f, "∃ {}", g),
      Form::Qtf(false,g) => write!(f, "∀ {}", g),
      Form::Rel(r,ts) => write!(f, "{}{}", r, Terms(ts))
    }
  }
}

pub enum FormPart {
  Cst(bool),
  Not,
  Qtf(bool),
  Bct(Bct),
  Rel(Rc<FS>, Vec<Term>)
} 

type Annot = Option<GT>;
pub type Inst = (String, bool, Form, Annot);

pub fn err_str<T>(s: &str) -> Rst<T> { Err(s.to_string()) }

pub fn to_boxed_slice(tptp: &str) -> Rst<Box<[u8]>> {
  let mut buffer = vec![];
  let mut file = match File::open(tptp) {
    Ok(x) => x,
     _ => return err_str("Cannot open TPTP file.")
  };
  match file.read_to_end(&mut buffer) {
    Ok(_) => (),
    _ => return err_str("Cannot read TPTP file to end")
  };
  Ok(buffer.into_boxed_slice())
}


/** Put Functions **/

pub fn put_char<W: Write>(w: &mut W, c: char) -> Rst<()> {
  match w.write(&[c as u8]) {
    Ok(_) => Ok(()),
    _ => err_str("Failed to write char")
  }
}

pub fn put_u64<W: Write>(w: &mut W, k: u64) -> Rst<()> {
  put_string(w, &k.to_string())
}

pub fn put_string<W: Write>(w: &mut W, s: &str) -> Rst<()> {
  for c in s.chars() { put_char(w, c)?; }
  put_char(w,'%')
}

pub fn put_bool<W: Write>(w: &mut W, b: bool) -> Rst<()> {
  if b { put_char(w,'1') } else { put_char(w,'0') }
  // match r {
  //   Role::Axiom => put_char(w,'A'),
  //   Role::Plain => put_char(w,'P')
  // }
}

pub fn put_gt<W: Write>(w: &mut W, t: &GT) -> Rst<()> {
  match t {
    GT::Fun(s,ts) => {
      put_char(w,'$')?;
      put_string(w,&s)?;
      put_vec(w,&ts)
    }
    GT::List(ts) => {
      put_char(w,';')?;
      put_vec(w,&ts)
    }
  }
}

impl Put for GT {
  fn put<W: Write>(w: &mut W, t: &Self) -> Rst<()> { put_gt(w,t) }
}

pub fn put_option<T: Put, W: Write>(w: &mut W, o: &Option<T>) -> Rst<()> {
  match o {
    Some(x) => {
      put_char(w,'1')?;
      T::put(w,x)
    },
    None => put_char(w,'0')
  }
}

pub fn put_inst<W: Write>(w: &mut W, i: &Inst) -> Rst<()> {
  put_string(w,&i.0)?;
  put_bool(w,i.1)?;
  put_form(w,&i.2)?;
  put_option(w,&i.3)
}

/** Get Functions **/

pub fn get_char(bs: ReadBytesRef) -> Rst<char> { 
  let c = char::from(get_byte(bs)?);
  // print!("{}", c);
  Ok(c)
}

fn get_byte(bs : ReadBytesRef) -> Rst<u8> {
  match bs.next() {
    Some(x) => match x {
      Ok(b) => Ok(b),
      _ => err_str("Cannot read next byte")
    },
    None => err_str("Cannot read next byte")
  }
}

fn get_fs(bs: ReadBytesRef) -> Rst<FS> {
  match get_char(bs)? {
    '"' => {
      let a = get_string(bs)?;
      Ok(FS::Atm(a))
    },
    '#' => {
      let k = get_u64(bs)?;
      Ok(FS::Par(k))
    },
    _ => err_str("Cannot parse functor")
  }
}

pub fn get_u64(bs : ReadBytesRef) -> Rst<u64> {
  let s = get_string(bs)?;
  match s.parse::<u64>() {
    Ok(k) => Ok(k),
    _ => err_str("Cannot parse String to u64")
  }
}

pub fn get_bool(bs: ReadBytesRef) -> Rst<bool> { 
  match get_char(bs)? {
    '1' => Ok(true),
    '0' => Ok(false),
     c  => Err(format!("Cannot parse bool from char = {}", c))
  }
}

fn bool_char(b: &bool) -> char { if *b { '1' } else { '0' } }

fn bct_char(b: &Bct) -> char {
  match b {
    Bct::Or => '|',
    Bct::And => '&',
    Bct::Imp => '>',
    Bct::Iff => '=',
  }
}

pub fn put_form<W: Write>(w: &mut W, f: &Form) -> Rst<()> {
  let mut fs: Vec<&Form> = vec![f];
  loop {
    match fs.pop() {
      Some(g) => {
        match g {
          Form::Cst(b) => { put_char(w,bool_char(b))?; },
          Form::Not(h) => {
            put_char(w,'~')?;
            fs.push(h);
          },
          Form::Bct(b,i,j) => {
            put_char(w,bct_char(b))?;
            fs.push(j);
            fs.push(i);
          }, 
          Form::Qtf(true,h) => {
            put_char(w,'?')?;
            fs.push(h);
          }, 
          Form::Qtf(false,h) => {
            put_char(w,'!')?;
            fs.push(h);
          }, 
          Form::Rel(ft,ts) => {
            put_char(w,'$')?;
            put_fs(w,&**ft)?;
            put_vec(w,ts)?;
          }
        };
      },
      _ => return Ok(())
    }
  }
}

fn put_fs<W: Write>(w: &mut W, f: &FS) -> Rst<()> { 
  match f {
    FS::Atm(s) => {
      put_char(w,'"')?;
      put_string(w,&s)
    },
    FS::Par(k) => {
      put_char(w,'#')?;
      put_u64(w,*k)
    }
  }
}

pub fn put_term<W: Write>(w: &mut W, t: &Term) -> Rst<()> {
  match t {
    Term::Var(k) => {
      put_char(w,'#')?;
      put_u64(w,*k)
    },
    // Term::Dst(s) => {
    //   put_char(w,'"')?;
    //   put_string(w,&s)
    // },
    // Term::Num(s) => {
    //   put_char(w,'#')?;
    //   put_string(w,&s)
    // },
    Term::Fun(f,ts) => {
      put_char(w,'$')?;
      put_fs(w,&*f)?;
      put_vec(w, ts)
    }
  }
}
  
pub fn get_term(bs : ReadBytesRef) -> Rst<Term> {
  match get_char(bs)? {
    '#' => {
      let n = get_u64(bs)?;
      Ok(Term::Var(n))
    },
    '$' => {
      let f = get_fs(bs)?;
      let ts = get_vec::<Term>(bs)?; 
      Ok(Term::Fun(Rc::new(f), ts))
    },
    _ => err_str("Cannot parse term")
  }
}

impl<'a> Conv<GT> for GeneralTerm<'a> {
  fn conv(t: GeneralTerm) -> Rst<GT> { conv_general_term(t) }
}

impl Get for Term {
  fn get(bs: ReadBytesRef) -> Rst<Term> { get_term(bs) }
}

impl Put for Term {
  fn put<W: Write>(w: &mut W, t: &Self) -> Rst<()> { put_term(w,t) }
}

pub fn get_string(bs : ReadBytesRef) -> Rst<String> {
  let mut c = get_char(bs)?;
  let mut s = String::from("");
  while c != '%' {
    s.push(c);
    c = get_char(bs)?;
  }
  Ok(s)
}

fn put_vec<P: Put, W: Write>(w: &mut W, v: &Vec<P>) -> Rst<()> {
  for x in v.into_iter() {
    put_char(w,',')?; 
    P::put(w,x)?;
  }
  put_char(w,'.')?;
  Ok(())
}
  
fn conv_vec<T, C: Conv<T>>(v: Vec<C>) -> Rst<Vec<T>> {
  v.into_iter().map(|x| C::conv(x)).collect()
}

fn get_vec<F: Get>(bs : ReadBytesRef) -> Rst<Vec<F>> {
  let mut c = get_char(bs)?; 
  let mut v = vec![];
  while c != '.' {
    if c != ',' { return err_str("Cannot get vector.") };
    let x = F::get(bs)?;
    v.push(x);
    c = get_char(bs)?;
  };
  Ok(v)
}

pub fn get_form(bs: ReadBytesRef) -> Rst<Form> {
  let mut rem: u64 = 1;
  let mut stk: Vec<FormPart> = vec![];
  while 0 < rem {
    match get_char(bs)? {
      '1' => {
         stk.push(FormPart::Cst(true));
         rem = rem - 1; 
      }, 
      '0' => {
         stk.push(FormPart::Cst(false));
         rem = rem - 1; 
      }, 
      '~' => stk.push(FormPart::Not),
      '!' => stk.push(FormPart::Qtf(false)),
      '?' => stk.push(FormPart::Qtf(true)),
      '|' => { stk.push(FormPart::Bct(Bct::Or)); rem = rem + 1; },
      '&' => { stk.push(FormPart::Bct(Bct::And)); rem = rem + 1; },
      '>' => { stk.push(FormPart::Bct(Bct::Imp)); rem = rem + 1; },
      '=' => { stk.push(FormPart::Bct(Bct::Iff)); rem = rem + 1; },
      '$' => {
        let f = get_fs(bs)?; 
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

fn build_form(mut ps: Vec<FormPart>) -> Option<Form> {
  let mut fs: Vec<Form> = vec![];
  loop {
    match ps.pop() {
      Some(p) => {
        match p {
          FormPart::Cst(b) => fs.push(Form::Cst(b)),
          FormPart::Not => {
            let f = fs.pop()?;
            fs.push(Form::Not(Rc::new(f)));
          },
          FormPart::Bct(b) => {
            let f = fs.pop()?;
            let g = fs.pop()?;
            fs.push(Form::Bct(b,Rc::new(f),Rc::new(g)));
          },
          FormPart::Qtf(q) => {
            let f = fs.pop()?;
            fs.push(Form::Qtf(q,Rc::new(f)));
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


// TODO : Find out whether `'foo'` and `foo` should be considered distinct 
fn conv_atomic_word(a: AtomicWord) -> String {
  match a {
    AtomicWord::Lower(LowerWord(w)) => w.to_string(),
    AtomicWord::SingleQuoted(SingleQuoted(w)) => format!("'{}'", w.to_string())
  }
}

fn conv_name(n: Name) -> Rst<String> {
  match n {
    Name::AtomicWord(a) => Ok(conv_atomic_word(a)),
    Name::Integer(Integer(i)) => Ok((*i).to_string())
    // {
    //   match (*i).parse::<u64>() {
    //     Ok(k) => Ok(NM::Num(k)),
    //     _ => err_str("String cannot be parsed into u64")
    //   }
    // }
  }
}

fn conjecturize(r: FormulaRole, f: Form) -> Form {
  match r {
    FormulaRole(LowerWord("conjecture")) => Form::Not(Rc::new(f)),  
    _ => f
  }
}

fn conv_fof_logic_formula(vs: &mut Vec<String>, f: fof::LogicFormula) -> Rst<Form> {
  match f {
    fof::LogicFormula::Binary(fof::BinaryFormula::Assoc(g)) => conv_fof_binary_assoc(vs,g),
    fof::LogicFormula::Binary(fof::BinaryFormula::Nonassoc(g)) => {
      match g {
        fof::BinaryNonassoc {left:lf,op:o,right:rf} => {
          let sz = vs.len();
          let nlf = conv_fof_unit_formula(vs,*lf)?;
          vs.truncate(sz);
          let nrf = conv_fof_unit_formula(vs,*rf)?;
          Ok(apply_non_assoc_connective(o,nlf,nrf))
        }
      }
    },
    fof::LogicFormula::Unary(g) => conv_fof_unary_formula(vs,g),
    fof::LogicFormula::Unitary(g) => conv_fof_unitary_formula(vs,g)
  }
}

fn string_args_term(s: String, ts: Vec<Term>) -> Term {
  Term::Fun(Rc::new(FS::Atm(s)),ts)
}

fn string_args_form(s: String, ts: Vec<Term>) -> Form {
  Form::Rel(Rc::new(FS::Atm(s)),ts)
}
  
fn apply_qtf(b: bool, f: Form) -> Form {
  Form::Qtf(b, Rc::new(f))
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

fn conv_fof_atomic_formula(vs: &Vec<String>, f: fof::AtomicFormula) -> Rst<Form> {
  match f {
    fof::AtomicFormula::Plain(g) => {
      match g {
        fof::PlainAtomicFormula {0: h} => {
          let (fs,ts) = conv_fof_plain_term(vs,h)?;
          Ok(Form::Rel(Rc::new(fs),ts))
        }
      }
    },
    fof::AtomicFormula::Defined(g) => {
      match g {
        fof::DefinedAtomicFormula::Plain(fof::DefinedPlainFormula(t)) => {
          let s = conv_fof_defined_plain_term(t);
          if s == "$true" { Ok(Form::Cst(true)) }
          else if s == "$false" { Ok(Form::Cst(false)) }
          else  { Ok(string_args_form(s,vec![])) }
        },
        fof::DefinedAtomicFormula::Infix(
          fof::DefinedInfixFormula {left: l, op: _, right: r}
        ) => {
          let t = conv_fof_term(vs,*l)?;
          let s = conv_fof_term(vs,*r)?;
          Ok(mk_eq(t,s))
        }
      }
    },
    fof::AtomicFormula::System(g) => {
      match g {
        fof::SystemAtomicFormula(h) => {
          match h {
            fof::SystemTerm::Constant(SystemConstant(ft)) => {
              Ok(Form::Rel(Rc::new(conv_system_functor(ft)),vec![]))
            },
            fof::SystemTerm::Function(i,j) => {
              Ok(Form::Rel(Rc::new(conv_system_functor(i)), conv_fof_arguments(vs,*j)?))
            }
          }
        }
      }
    }
  }
}

fn conv_fof_unitary_formula(vs: &mut Vec<String>, f: fof::UnitaryFormula) -> Rst<Form> {
  match f {
    fof::UnitaryFormula::Quantified(fof::QuantifiedFormula {quantifier: q, bound: fof::VariableList(l), formula: g}) => {
      let ss: Vec<String> = l.iter().map(|x| conv_variable(x)).collect();
      let lth = ss.len();
      vs.extend(ss);
      let mut h: Form = conv_fof_unit_formula(vs,*g)?;
      for _ in 0..lth { h = apply_qtf(conv_fof_quantifier(q),h); }
      Ok(h)
    },
    fof::UnitaryFormula::Atomic(g) => conv_fof_atomic_formula(vs,*g),
    fof::UnitaryFormula::Parenthesised(g) => conv_fof_logic_formula(vs,*g)
  }
}

fn conv_fof_binary_assoc(vs: &mut Vec<String>, f: fof::BinaryAssoc) -> Rst<Form> {
  match f {
    fof::BinaryAssoc::Or(fof::OrFormula {0: fs}) => conv_vec_unit_formula(vs,Bct::Or,fs),
    fof::BinaryAssoc::And(fof::AndFormula {0: fs}) => conv_vec_unit_formula(vs,Bct::And,fs)
  }
}
  
fn conv_fof_formula(vs: &mut Vec<String>, f: fof::Formula) -> Rst<Form> {
  match f { fof::Formula {0: g} => conv_fof_logic_formula(vs,g) }
}

fn conv_role(r: &FormulaRole) -> bool {
  let FormulaRole(LowerWord(s)) = r;
  match s {
    &"axiom" => true,
    &"lemma" => true,
    &"hypothesis" => true,
    &"conjecture" => true,
    &"negated_conjecture" => true,
    &"definition" => true,
    _ => false
  }
}

// fn conv_general_list(l: GeneralList) -> Rst<GT> {
//   match l {
//     GeneralList(v) => {
// 
//     }
//   }
// }

fn conv_general_data (d: GeneralData) -> Rst<GT> {
  match d {
    GeneralData::Atomic(a) => Ok(GT::Fun(conv_atomic_word(a),vec![])),
    GeneralData::Function(f) => {
      Ok(GT::Fun(conv_atomic_word(f.word),conv_general_terms(f.terms)?))
    },
    _ => unimplemented!()
  }
}

fn conv_general_terms (ts: GeneralTerms) -> Rst<Vec<GT>> { conv_vec(ts.0) }

fn conv_general_term (t: GeneralTerm) -> Rst<GT> {
  match t {
    GeneralTerm::Data(d) => conv_general_data(d),
    GeneralTerm::Colon(_,_) => unimplemented!(),
    GeneralTerm::List(GeneralList(Some(ts))) => Ok(GT::List(conv_general_terms(ts)?)),
    GeneralTerm::List(GeneralList(None)) => Ok(GT::List(vec![]))
  }
}

fn conv_annotations (a: Annotations) -> Rst<Annot> {
  match a {
    Annotations(Some(b)) => {
      match *b {
        (Source(t), _) => Ok(Some(conv_general_term(t)?))
      }
    },
    Annotations(None) => Ok(None)
  }
}

// pub fn conv_annotated_formula_to_hyp(a: AnnotatedFormula) -> Rst<(String, Form)> {
//   let (n,_,f,_) = conv_annotated_formula(a)?;
//   Ok((n,f))
// }

pub fn conv_annotated_formula(a: AnnotatedFormula) -> Rst<Inst> {
  match a {
    AnnotatedFormula::Fof(b) => {
      match *b {
        FofAnnotated(Annotated {name: n, role: r, formula: f, annotations: a}) => {
          Ok((
            conv_name(n)?, 
            conv_role(&r),
            conjecturize(r, conv_fof_formula(&mut vec![], *f)?),
            conv_annotations(a)?
          ))
        }
      }
    },
    AnnotatedFormula::Cnf(b) => {
      match *b {
        CnfAnnotated(Annotated {name: n, role: r, formula: f, annotations: a}) => {
          let g = match *f {
            cnf::Formula::Disjunction(cnf::Disjunction(g)) => g,
            cnf::Formula::Parenthesised(cnf::Disjunction(g)) => g
          };
          Ok((
            conv_name(n)?, 
            conv_role(&r),
            conjecturize(r, conv_literals(g)?),
            conv_annotations(a)?
          ))
        }
      }
    }
  }
}

fn conv_fof_unit_formula(vs: &mut Vec<String>, f: fof::UnitFormula) -> Rst<Form> { 
  match f {
    fof::UnitFormula::Unary(g) => conv_fof_unary_formula(vs,g),
    fof::UnitFormula::Unitary(g) => conv_fof_unitary_formula(vs,g),
  }
}

fn conv_number(n: Number) -> String {
  match n {
    Number::Integer(Integer(s)) => s.to_string(),
    Number::Rational(Rational(s)) => s.to_string(),
    Number::Real(Real(s)) => s.to_string()
  }
}


fn find_variable_index(vs: &Vec<String>, v: Variable) -> Rst<u64> {
  let s = conv_variable(&v);
  // let ei = vs.len() - 1;
  match vs.iter().rev().position(|x| *x == s) {
    Some(i) => {
      match u64::try_from(i) {
        Ok(x) => Ok(x),
        _ => err_str("Cannot convert usize to u64")
      }
    }, 
    _ => err_str("Unbound variable")
  }
}

fn conv_fof_term(vs: &Vec<String>, t: fof::Term) -> Rst<Term> {
  match t {
    fof::Term::Variable(v) => {
      let u = find_variable_index(vs, v)?;
      Ok(Term::Var(u))
    },
    fof::Term::Function(s) => {
      match *s {
        fof::FunctionTerm::Defined(r) => {
          match r {
            fof::DefinedTerm::Atomic(fof::DefinedAtomicTerm(t)) => Ok(string_args_term(conv_fof_defined_plain_term(t),vec![])),
            fof::DefinedTerm::Defined(q)=> {
              match q {
                DefinedTerm::Distinct(DistinctObject(p)) => Ok(string_args_term(format!("\"{}\"", (*p).to_string()),vec![])),
                DefinedTerm::Number(p) => Ok(string_args_term(conv_number(p),vec![]))
              }
            }
          }
        },
        fof::FunctionTerm::Plain(r) => {
          let (fs,ts) = conv_fof_plain_term(vs, r)?;
          Ok(Term::Fun(Rc::new(fs),ts))
        },
        fof::FunctionTerm::System(r) => conv_fof_system_term(vs, r)
      }
    }
  }
}

fn conv_fof_infix_unary(vs: &Vec<String>, f: fof::InfixUnary) -> Rst<Form> {
  match f {
    fof::InfixUnary {left: l, op: _, right: r} => {
      let t = conv_fof_term(vs,*l)?;
      let s = conv_fof_term(vs,*r)?;
      Ok(Form::Not(Rc::new(mk_eq(t,s))))
    }
  }
}

fn conv_fof_unary_formula(vs: &mut Vec<String>, f: fof::UnaryFormula) -> Rst<Form> {
  match f {
    fof::UnaryFormula::Unary(_,g) => Ok(Form::Not(Rc::new(conv_fof_unit_formula(vs,*g)?))),
    fof::UnaryFormula::InfixUnary(g) => conv_fof_infix_unary(vs,g)
  }
}

fn conv_fof_quantifier(q: fof::Quantifier) -> bool {
  match q {
    fof::Quantifier::Forall => false,
    fof::Quantifier::Exists => true
  }
}

fn conv_variable(v: &Variable) -> String {
  match v { Variable {0: UpperWord {0: s}} => s.to_string() }
}

fn conv_functor(f: Functor) -> FS {
  match f { Functor(a) => FS::Atm(conv_atomic_word(a)) }
}
  
fn conv_fof_arguments(vs: &Vec<String>, f: fof::Arguments) -> Rst<Vec<Term>> {
  match f { fof::Arguments(g) => g.into_iter().map(|x| conv_fof_term(vs,x)).collect() }
}

fn conv_fof_system_term(vs: &Vec<String>, t: fof::SystemTerm) -> Rst<Term> {
  match t {
    fof::SystemTerm::Constant(common::SystemConstant(f)) => {
      Ok(Term::Fun(Rc::new(conv_system_functor(f)), vec![]))
    }
    fof::SystemTerm::Function(f, a) => {
      let ts = conv_fof_arguments(vs, *a)?;
      Ok(Term::Fun(Rc::new(conv_system_functor(f)), ts))
    }
  }
}

fn conv_fof_plain_term(vs: &Vec<String>, f: fof::PlainTerm) -> Rst<(FS,Vec<Term>)> {
  match f {
    fof::PlainTerm::Constant(Constant(g)) => {
      Ok((conv_functor(g),vec![]))
    },
    fof::PlainTerm::Function(g,h) => {
      Ok((conv_functor(g),conv_fof_arguments(vs,*h)?))
    }
  }
}

fn conv_fof_defined_plain_term(t: fof::DefinedPlainTerm) -> String {
  match t {
    fof::DefinedPlainTerm::Constant(
      DefinedConstant(
        DefinedFunctor(
          AtomicDefinedWord(
            DollarWord(
              LowerWord(s)
            )
          )
        )
      )
    ) => format!("${}", s),
    fof::DefinedPlainTerm::Function(_, _) => panic!("Conversion for defined complex terms not implemented")
  } 
}
  
fn conv_system_functor(f: SystemFunctor) -> FS {
  match f {
    SystemFunctor(AtomicSystemWord(DollarDollarWord(LowerWord(s)))) =>
    FS::Atm(format!("$${}",s))
  }
}

fn conv_vec_unit_formula(vs: &mut Vec<String>, b: Bct, fs: Vec<fof::UnitFormula>) -> Rst<Form> {
  let sz = vs.len();
  let gs: Rst<Vec<Form>> = fs.into_iter().map(|x| {vs.truncate(sz); conv_fof_unit_formula(vs,x)}).collect();
  chain_forms(b,gs?)
}

fn conv_literal(vs: &Vec<String>, l: cnf::Literal) -> Rst<Form> {
  match l {
    cnf::Literal::Atomic(f) => conv_fof_atomic_formula(vs,f),
    cnf::Literal::NegatedAtomic(f) => Ok(Form::Not(Rc::new(conv_fof_atomic_formula(vs,f)?))),
    cnf::Literal::Infix(f) => conv_fof_infix_unary(vs,f) 
  }
}

fn conv_literals(ls: Vec<cnf::Literal>) -> Rst<Form> {
  let mut vs: Vec<String> = vec![];
  for l in ls.iter() {
    vars_in_literal(&mut vs, l);
  }
  let k = vs.len();
  let fs: Rst<Vec<Form>> = ls.into_iter().map(|x| conv_literal(&vs,x)).collect();
  let mut f = chain_forms(Bct::Or, fs?)?;
  for _ in 0..k {
    f = Form::Qtf(false,Rc::new(f));
  }
  Ok(f)
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
  
fn mk_eq(t: Term, s: Term) -> Form { 
  Form::Rel(Rc::new(FS::Atm("=".to_string())), vec![t,s])
}
  
pub fn is_eq(t: Term, s: Term, f: &Form) -> bool { 
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

fn vars_in_fof_arguments(vs: &mut Vec<String>, f: &fof::Arguments) -> () {
  match f { fof::Arguments(ts) => { for t in ts.iter() { vars_in_term(vs,t); } } }
}

fn vars_in_term(vs: &mut Vec<String>, t: &fof::Term) -> () {
  match t {
    fof::Term::Variable(v) => {
      let s = conv_variable(v);
      if !vs.contains(&s) { vs.push(s) }
    },
    fof::Term::Function(s) => {
      match &**s {
        fof::FunctionTerm::Defined(_) => (),
        fof::FunctionTerm::Plain(r) => vars_in_fof_plain_term(vs,r),
        fof::FunctionTerm::System(r) => vars_in_fof_system_term(vs,r)
      }
    }
  }
}

fn vars_in_fof_atomic_formula(vs: &mut Vec<String>, f: &fof::AtomicFormula) -> () {
  match f {
    fof::AtomicFormula::System(g) => {
      match &*g {
        fof::SystemAtomicFormula(h) => {
          match h {
            fof::SystemTerm::Constant(_) => (),
            fof::SystemTerm::Function(_,i) => vars_in_fof_arguments(vs,i)
          }
        }
      }
    }
    fof::AtomicFormula::Defined(g) => {
      match &*g {
        fof::DefinedAtomicFormula::Infix(h) => {
          match h {
            fof::DefinedInfixFormula {left:lt, op: _, right: rt} => {
              vars_in_term(vs,&lt);
              vars_in_term(vs,&rt);
            }
          }
        },
        fof::DefinedAtomicFormula::Plain(_) => ()
      }
    },
    fof::AtomicFormula::Plain(g) => {
      match &*g { fof::PlainAtomicFormula(h) => vars_in_fof_plain_term(vs,h) }
    }
  }
}

fn vars_in_fof_plain_term(vs: &mut Vec<String>, t: &fof::PlainTerm) -> () {
  match t {
    fof::PlainTerm::Constant(_) => (),
    fof::PlainTerm::Function(_,i)=> vars_in_fof_arguments(vs,i)
  }
}

fn vars_in_fof_system_term(vs: &mut Vec<String>, t: &fof::SystemTerm) -> () {
  match t {
    fof::SystemTerm::Constant(_) => (),
    fof::SystemTerm::Function(_, a) => vars_in_fof_arguments(vs, a)
  }
}

fn vars_in_literal(vs: &mut Vec<String>, l: &cnf::Literal) -> () {
  match l {
    cnf::Literal::Atomic(f) => vars_in_fof_atomic_formula(vs,f),
    cnf::Literal::NegatedAtomic(f) => vars_in_fof_atomic_formula(vs,f),
    cnf::Literal::Infix(fof::InfixUnary {left: lt, op: _, right: rt}) => {
      vars_in_term(vs,&lt);
      vars_in_term(vs,&rt);
    }
  }
}

fn conv_tptp_input(t: TPTPInput, fs: &mut Vec<Inst>) {
  match t {
    TPTPInput::Annotated(a) => fs.push(conv_annotated_formula(*a).expect("Cannot convert annotated formula")),
    TPTPInput::Include(b) => {
      match *b {
        Include {file_name: FileName(SingleQuoted(s)), selection: _} => {
          let tptp = env::var("TPTP").expect("Env var $TPTP not set");
          let pt: String = format!("{}/{}", tptp, s);
          conv_tptp_file_core(&pt, fs);
        }
      }
    }
  }
}

pub fn conv_tptp_file_core(tptp: &str, fs: &mut Vec<Inst>) {
  println!("Opening TPTP file = {}", tptp);
  
  let bytes = to_boxed_slice(tptp).expect("Cannot open TPTP file");
  let mut is = TPTPIterator::<()>::new(&bytes);
  for x in &mut is {
    match x {
      Ok(i) => conv_tptp_input(i,fs),
      _ => panic!("Invalid item from TPTP problem file")
    }
  }
  assert!(is.remaining.is_empty());
}

pub fn conv_tptp_file(tptp: &str) -> Vec<Inst> {
  let mut fs: Vec<Inst> = vec![];
  conv_tptp_file_core(tptp, &mut fs);
  fs
}