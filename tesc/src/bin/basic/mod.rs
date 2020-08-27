use std::rc::Rc;
use std::io::{BufReader, BufWriter};
use std::fs::File;
use std::io;
use std::mem::swap;
use std::io::{Read, Write};
use tptp::parsers::TPTPIterator;
use tptp::syntax::*;

#[derive(Debug)]
pub enum Dir {Lft, Rgt}

#[derive(PartialEq, Clone, Debug)]
pub enum FS {
  Par(u64),
  Atm(String),
}

#[derive(PartialEq, Clone, Debug)]
pub enum Term {
  Var(u64),
  Fun(Rc<FS>, Vec<Term>),
  Dst(Rc<String>),
  Num(Rc<String>)
}

#[derive(PartialEq, Clone, Debug, Copy)]
pub enum Bct {Or, And, Imp, Iff}

#[derive(PartialEq, Clone, Debug, Copy)]
pub enum Qtf {Fa, Ex}

#[derive(PartialEq, Clone, Debug)]
pub enum Form {
  Cst(bool),
  Not(Rc<Form>),
  Bct(Bct, Rc<Form>, Rc<Form>),
  Qtf(Qtf, Rc<Form>),
  Rel(Rc<FS>, Vec<Term>)
} 

pub enum FormPart {
  Cst(bool),
  Not,
  Qtf(Qtf),
  Bct(Bct),
  Rel(Rc<FS>, Vec<Term>)
} 

#[derive(PartialEq, Eq, std::hash::Hash, Clone, Debug)]
pub enum ID {
  Atm(String),
  Num(u64),
  Par(u64)
} 

pub type WriteBytes<'a> = &'a mut BufWriter<File>;
pub type FileBytes<'a> = &'a mut io::Bytes<io::BufReader<File>>;
pub type Rst<T> = Result<T, String>;

pub fn err_str<T>(s: &str) -> Rst<T> { 
  Err(s.to_string())
}

trait Get { fn get(_: FileBytes) -> Rst<Self> where Self: std::marker::Sized; }

pub fn to_boxed_slice(tptp: &str) -> Result<Box<[u8]>, String> {
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

fn put_char(wb: WriteBytes, c: char) -> Rst<()> {
  // let f = File::create("/tmp/foo").expect("Unable to create file");
  // let mut f = BufWriter::new(f);
  match wb.write(&[c as u8]) {
    Ok(_) => Ok(()),
    _ => err_str("Failed to write char")
  }
}

fn put_string(wb: WriteBytes, s: String) -> Rst<()> {
  for c in s.chars() { put_char(wb, c)?; }
  Ok(())
}

fn put_id(wb: WriteBytes, i: ID) -> Rst<()> {
  match i {
    ID::Atm(s) => {
      put_char(wb, '\'')?;
      put_string(wb, s)?;
    },
    ID::Num(k) => {
      put_char(wb, '#')?;
      put_string(wb, k.to_string())?;
    },
    ID::Par(k) => {
      put_char(wb, '#')?;
      put_string(wb, k.to_string())?;
    }
  }
  Ok(())
}


/** Get Functions **/

pub fn get_char(bs: FileBytes) -> Rst<char> { 
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

fn get_fs(bs: FileBytes) -> Rst<FS> {
  match get_char(bs)? {
    '\'' => {
      let a = get_string(bs)?;
      Ok(FS::Atm(a))
    },
    '@' => {
      let k = get_u64(bs)?;
      Ok(FS::Par(k))
    },
    _ => err_str("Cannot parse functor")
  }
}

pub fn get_sign(bs: FileBytes) -> Rst<bool> {
  match get_char(bs)? {
    '+' => Ok(true),
    '-' => Ok(false),
    _ => err_str("Cannot parse sign")
  }
}

fn get_u64(bs : FileBytes) -> Result<u64, String> {
  let s = get_string(bs)?;
  match s.parse::<u64>() {
    Ok(k) => Ok(k),
    _ => err_str("Cannot parse String to u64")
  }
}

pub fn get_dir(bs: FileBytes) -> Rst<Dir> { 
  match get_char(bs)? {
    '<' => Ok(Dir::Lft),
    '>' => Ok(Dir::Rgt),
     c  => Err(format!("Cannot parse direction from char = {}", c))
  }
}

pub fn get_id(bs: FileBytes) -> Rst<ID> { 
  match get_char(bs)? {
    '\'' => {
      let a = get_string(bs)?;
      Ok(ID::Atm(a))
    }
    '@' => {
      let k = get_u64(bs)?;
      Ok(ID::Par(k))
    },
    '#' => {
      let k = get_u64(bs)?;
      Ok(ID::Num(k))
    },
    _ => err_str("Cannot parse name")
  }
}

pub fn get_term(bs : FileBytes) -> Rst<Term> {
  match get_char(bs)? {
    '#' => {
      let n = get_u64(bs)?;
      Ok(Term::Var(n))
    },
    '^' => {
      let f = get_fs(bs)?;
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
  fn get(bs: FileBytes) -> Rst<Term> { get_term(bs) }
}

fn get_string(bs : FileBytes) -> Rst<String> {
  let mut c = get_char(bs)?;
  let mut s = String::from("");
  while c != '$' {
    s.push(c);
    c = get_char(bs)?;
  }
  Ok(s)
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

pub fn get_form(bs: FileBytes) -> Rst<Form> {
  let mut rem: u64 = 1;
  let mut stk: Vec<FormPart> = vec![];
  while 0 < rem {
    match get_char(bs)? {
      'T' => {
         stk.push(FormPart::Cst(true));
         rem = rem - 1; 
      }, 
      'F' => {
         stk.push(FormPart::Cst(false));
         rem = rem - 1; 
      }, 
      '~' => stk.push(FormPart::Not),
      '!' => stk.push(FormPart::Qtf(Qtf::Fa)),
      '?' => stk.push(FormPart::Qtf(Qtf::Ex)),
      '|' => { stk.push(FormPart::Bct(Bct::Or)); rem = rem + 1; },
      '&' => { stk.push(FormPart::Bct(Bct::And)); rem = rem + 1; },
      '>' => { stk.push(FormPart::Bct(Bct::Imp)); rem = rem + 1; },
      '=' => { stk.push(FormPart::Bct(Bct::Iff)); rem = rem + 1; },
      '^' => {
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

struct ProbStack<'a> {
  top: TPTPIterator<'a,()>,
  rest: Vec<TPTPIterator<'a,()>>
}

/*
impl<'a> Iterator for ProbStack<'a> {
  type Item = AnnotatedFormula<'a>;
  fn next(&mut self) -> Option<AnnotatedFormula<'a>> {
    match self.top.next() {
      Some(r) => {
        match r.expect("Error reading TPTP") {
          TPTPInput::Annotated(a) => Some(a),
          TPTPInput::Include(Include {file_name: FileName(SingleQuoted(i)), selection: _}) => {
            let bytes = to_boxed_slice(&i).expect("Cannot open file");
            let mut p = TPTPIterator::<()>::new(&bytes);
            swap(&mut self.top, &mut p);
            self.rest.push(p);
            self.next()
          }
        }
      },
      None => {
        match self.rest.pop() {
          Some(p) => {
            self.top = p;
            self.next()
          },
          None => None
        }
      }
    }
  }
}
*/