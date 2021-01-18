use super::basic::*;
use std::collections::HashMap;

struct TempIter<'a>(ReadBytesRef<'a>);

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

enum Mode {id, fi}

fn update(m: Mode, off: u64, red: Redirect, k: u64) -> u64 {
  unimplemented!()
}

fn relabel(tab: NameTable, off: u64, red: Redirect, temp: ReadBytesRef, tesc: WriteBytesRef) -> Rst<()> {
  let mut conts: Vec<u64> = vec![];
  let mut it = TempIter(temp);
   
  loop {
    match it.next().expect("Unexpected end of temp file") {
      TempStep::A(i,b) => {
        put_u64(tesc, update(Mode::id, off, red, i))?;
        put_bool(tesc, b)?;
      }
    }
  }
}

pub fn main<I: Iterator<Item=String>>(mut args: I) -> Rst<()> {

  let tptp_path = args.next().expect("missing TPTP file");
  let temp_path = args.next().expect("missing TEMP file");
  let tesc_path = args.next().expect("missing TESC file");

  // let mut origs: Redirect = vec![];
  // let mut tab: HashMap<String, u64> = HashMap::new();

  let is = conv_tptp_file(&tptp_path);
  let off = is.len();
  let tab: HashMap<String, u64> = build_name_table(is);

  let mut temp = get_read_bytes(&temp_path, "Cannot open temp file"); 
  let mut tesc = get_read_bytes(&tesc_path, "Cannot open TESC file"); 
  let mut tesc = get_write_bytes(&tesc_path, "Cannot create TESC file");
  
  relabel(tab, off, vec![], temp, tesc) 
}