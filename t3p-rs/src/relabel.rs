use super::basic::*;
use std::rc::Rc;
use std::collections::HashMap;

struct TempIter<'a>(ReadBytesRef<'a>);

enum Step {
  A(u64,bool),
  B(u64),
  C(u64,Term),
  D(u64),
  N(u64),
  S(Form),
  T(Form),
  X(u64, u64)
}

enum TempStep {
  A(u64,bool),
  B(u64),
  C(u64,Term),
  D(u64),
  N(u64),
  P(String),
  S(Form),
  T(Form),
  X(u64, u64)
}

impl<'a> TempIter<'a> {
  fn next_core(&mut self) -> Rst<TempStep> {
    match get_char(self.0)? {
      'A' => {
        let k = get_u64(self.0)?;
        let b = get_bool(self.0)?;
        Ok(TempStep::A(k,b))
      },
      'B' => {
        let k = get_u64(self.0)?;
        Ok(TempStep::B(k))
      },
      'C' => {
        let k = get_u64(self.0)?;
        let t = get_term(self.0)?;
        Ok(TempStep::C(k,t))
      }
      'D' => {
        let k = get_u64(self.0)?;
        Ok(TempStep::D(k))
      },
      'N' => {
        let k = get_u64(self.0)?;
        Ok(TempStep::N(k))
      },
      'P' => {
        let s = get_string(self.0)?;
        Ok(TempStep::P(s))
      },
      'S' => {
        let f = get_form(self.0)?;
        Ok(TempStep::S(f))
      },
      'T' => {
        let f = get_form(self.0)?;
        Ok(TempStep::T(f))
      },
      'X' => {
        let i = get_u64(self.0)?;
        let j = get_u64(self.0)?;
        Ok(TempStep::X(i,j))
      },
      _ => err_str("Invalid first character of step")
    }
  }
}

impl<'a> Iterator for TempIter<'a> {
  type Item = TempStep;

  fn next(&mut self) -> Option<Self::Item> {
    match self.next_core() {
      Ok(s) => Some(s),
      _ => None
    }
  }
}

type NameTable = HashMap<String, u64>;
type Redirect = Vec<(u64, u64)>;

fn build_name_table(is: Vec<Inst>) -> NameTable 
{
  let mut t: NameTable = HashMap::new();
  let mut k: u64 = 0;

  for (n, _, _, _) in is.into_iter() {
    t.insert(n, k);
    k = k + 1;
  }

  t
}

enum Mode {Id, Fi}

fn update_ftr(off: u64, red: &Redirect, f: Rc<FS>) -> Rc<FS> 
{
  match *f 
  {
    FS::Par(k) => Rc::new(FS::Par(update(Mode::Fi, off, red, k))),
    _ => f
  }
}

fn update_term(off: u64, red: &Redirect, t: &Term) -> Term {
  match t 
  {
    Term::Fun(f,ts) => 
      Term::Fun(
        update_ftr(off, red, f.clone()), 
        ts.into_iter().map(|x| update_term(off, red, x)).collect()
      ),
    Term::Var(k) => Term::Var(*k)
  }
}

fn update_form(off: u64, red: &Redirect, f: &Form) -> Form {
  match &*f {
    Form::Cst(b) => Form::Cst(*b),
    Form::Not(g) => Form::Not(Rc::new(update_form(off, red, &g))),
    Form::Bct(b,g,h) => 
      Form::Bct(
        *b,
        Rc::new(update_form(off, red, &g)),
        Rc::new(update_form(off, red, &h))
      ),
    Form::Qtf(q,g) => Form::Qtf(*q, Rc::new(update_form(off, red, &g))),
    Form::Rel(r,ts) => 
      Form::Rel(
        update_ftr(off, red, r.clone()), 
        ts.into_iter().map(|x| update_term(off, red, x)).collect()
      )
  }
}

fn update(m: Mode, off: u64, red: &Redirect, k: u64) -> u64 
{
  let mut p_before: u64 = 0;

  for (i,j) in red 
  {
    if k == *i 
    {
      match m 
      {
        Mode::Id => return *j,
        Mode::Fi => panic!("P and D rules superposed")
      }
    }  
    if k < *i { return (off + k) - p_before }
    p_before = p_before + 1;
  }
   
  (off + k) - p_before
}

struct RedIter<'a> {
  end: bool,
  tab: NameTable,
  off: u64, 
  red: Redirect, 
  conts: Vec<(u64, u64)>, 
  ti: TempIter<'a>,
  cnt: u64
}

impl<'a> Iterator for RedIter<'a> 
{
  type Item = Step;

  fn next(&mut self) -> Option<Self::Item> {
    if self.end { return None };
    let sav = self.cnt;
    self.cnt = self.cnt + 1;
    match self.ti.next()? {
      TempStep::A(i,b) => Some(Step::A(update(Mode::Id, self.off, &self.red, i), b)),
      TempStep::B(i)   => {
        let s = Step::B(update(Mode::Id, self.off, &self.red, i));
        self.conts.push((self.cnt, self.red.len() as u64));
        Some(s)
      }, 
      TempStep::C(i,t) => Some(Step::C(update(Mode::Id, self.off, &self.red, i), update_term(self.off, &self.red, &t))),
      TempStep::D(i)   => Some(Step::D(update(Mode::Id, self.off, &self.red, i))),
      TempStep::N(i)   => Some(Step::N(update(Mode::Id, self.off, &self.red, i))),
      TempStep::P(s)   => {
        let i = self.tab.get(&s)?;
        self.red.push((sav, *i));
        self.next()
      },
      TempStep::S(f)   => {
        let s = Step::S(update_form(self.off, &self.red, &f));
        self.conts.push((self.cnt, self.red.len() as u64));
        Some(s)
      },
      TempStep::T(f)   => Some(Step::T(update_form(self.off, &self.red, &f))),
      TempStep::X(i,j) => { 
        let s = Step::X(update(Mode::Id, self.off, &self.red, i), update(Mode::Id, self.off, &self.red, j));
        match self.conts.pop() {
          Some((sav_cnt, sav_len)) => {
            self.red.truncate(sav_len as usize);
            self.cnt = sav_cnt;
          }
          _ => { self.end = true }
        };
        Some(s)
      }
    }
  }
}

fn put_step(w: WriteBytesRef, s: Step) -> Rst<()> {
  match s {
    Step::A(i,b) => 
    {
      put_char(w,'A')?;
      put_u64(w,i)?;
      put_bool(w,b)
    },
    Step::B(i) => 
    {
      put_char(w,'B')?;
      put_u64(w,i)
    },
    Step::C(i,t) => 
    {
      put_char(w,'C')?;
      put_u64(w,i)?;
      put_term(w,&t)
    },
    Step::D(i) => 
    {
      put_char(w,'D')?;
      put_u64(w,i)
    },
    Step::N(i) => 
    {
      put_char(w,'N')?;
      put_u64(w,i)
    },
    Step::S(f) => 
    {
      put_char(w,'S')?;
      put_form(w,&f)
    },
    Step::T(f) => 
    {
      put_char(w,'T')?;
      put_form(w,&f)
    },
    Step::X(i,j) => 
    {
      put_char(w,'X')?;
      put_u64(w,i)?;
      put_u64(w,j)
    }
  }
}

pub fn main<I: Iterator<Item=String>>(mut args: I) -> Rst<()> 
{
  let tptp_path = args.next().expect("missing TPTP file");
  let temp_path = args.next().expect("missing TEMP file");
  let tesc_path = args.next().expect("missing TESC file");

  let is = conv_tptp_file(&tptp_path);
  let is_len = is.len() as u64;

  let mut temp = get_read_bytes(&temp_path, "Cannot open temp file"); 
  let mut tesc = get_write_bytes(&tesc_path, "Cannot create TESC file");

  let si: RedIter = RedIter {
    end: false,
    off: is_len,
    red: vec![],
    tab: build_name_table(is),
    cnt: 0, 
    conts: vec![],
    ti: TempIter(&mut temp)
  };

  for s in si { put_step(&mut tesc, s)?; };

  Ok(())
}