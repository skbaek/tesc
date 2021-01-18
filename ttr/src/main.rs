use std::env;
use std::io::prelude::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use tptp::syntax::*;
use tptp::parsers::TPTPIterator;
use basic::*;

type NameTable = HashMap<String, u64>;

fn add_tptp_input(t: TPTPInput, tab: &mut NameTable) -> Rst<()> {
  match t {
    TPTPInput::Annotated(a) => { 
      if let (_,true,f,None) = conv_annotated_formula(a)? {
        if !form_below(0, &f) { return err_str("Bad formula in TPTP problem.") };
        push_conc(bch, Rc::new(f));
        Ok(())
      } else {
        err_str("Non-axiom in TPTP problem.")
      }
    },
    TPTPInput::Include(Include {file_name: FileName(SingleQuoted(s)), selection: _}) => {
      let pt: String = format!("{}{}", folders::TPTP, s);
      add_tptp_file(&pt, bch)
    }
  }
}

fn add_tptp(tptp: &str, tab: &mut HashMap<&str, u64>) -> Rst<u64> {
   let bytes = to_boxed_slice(tptp)?;
   let mut is = TPTPIterator::<()>::new(&bytes);
   let mut off: u64 = 0;

   for x in &mut is {
     match x {
       Ok(i) => add_tptp_input(i, tab)?,
       _ => return err_str("Invalid item from TPTP problem file")
     }
   }
   assert!(is.remaining.is_empty());

   Ok(off)
}

fn relabel(
  mut tab: HashMap<&str, u64>, 
  off: u64, 
  mut origs: Vec<(u64, u64)>, 
  mut temp: std::io::Bytes<std::io::BufReader<std::fs::File>>,
  mut tesc: std::io::BufWriter<std::fs::File>
)
{
} 

fn main() {

  let args: Vec<String> = env::args().collect();
  let tptp_path = &args[1];
  let temp_path = &args[2];
  let tesc_path = &args[3];
  let mut origs: Vec<(u64, u64)> = vec![];
  let mut tab: HashMap<&str, u64> = HashMap::new();

  let off = add_tptp(tptp_path, &mut tab).expect("Cannot open TPTP file");

  let mut temp = BufReader::new(File::open(temp_path).expect("Cannot open temp file")).bytes(); 
  
  let mut tesc = BufWriter::new(File::create(tesc_path).expect("Cannot create TESC file"));

  relabel(tab, off, origs, temp, tesc); 

}
