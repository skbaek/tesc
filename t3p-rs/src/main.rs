mod basic;
mod serialize; 
mod relabel;
mod verify;

use basic::Rst;
use std::env;

fn main() -> Rst<()> {
  let mut args = env::args().skip(1);
  match args.next().expect("expected a subcommand").as_str() {
    "serialize" => serialize::main(args),
    "relabel" => relabel::main(args),
    "verify" => verify::main(args),
    _ => panic!("{}", "incorrect subcommand, expected {serialize, relabel, verify}")
  }
}
