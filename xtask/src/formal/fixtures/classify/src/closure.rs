//! A closure given to a combinator.

pub enum Error {
    InvalidState,
    Missing,
}

pub fn index_of(processes: &[u64; 4], process: u64) -> Result<usize, Error> {
    let mut index = 0;
    while index < 4 {
        if processes[index] == process {
            return Ok(index);
        }
        index += 1;
    }
    Err(Error::Missing)
}

pub fn owner(processes: &[u64; 4], process: u64) -> Result<usize, Error> {
    index_of(processes, process).map_err(|_| Error::InvalidState)
}
