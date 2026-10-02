use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};

use std::thread;
use std::time::Duration;

const N: usize = 3;


struct Bakery {
    flag: [AtomicBool; N],
    number: [AtomicUsize; N],
}

impl Bakery{
    fn new() -> Self {
     Self{

        flag: std::array::from_fn(|_| AtomicBool::new(false)),
        number: std::array::from_fn(|_| AtomicUsize::new(0)),
        }
    }

    fn lock(&self, id: usize) {
        self.flag[id].store(true, Ordering::SeqCst);
        let max_number = self
        .number
        .iter()
        .map(|n| n.load(Ordering::SeqCst))
        .max()
        .unwrap_or(0);
    

        self.number[id].store(max_number + 1, Ordering::SeqCst);
        self.flag[id].store(false, Ordering::SeqCst);

        for j in 0..N {
            if j == id {
                continue;
            }

            while self.flag[j].load(Ordering::SeqCst){
                thread::yield_now();
            }

            loop{
                let other_number = self.number[j].load(Ordering::SeqCst);
                let my_number = self.number[id].load(Ordering::SeqCst);

                if other_number == 0
                    || (other_number, j) >= (my_number, id)
                    {
                        break;
                    }
                    thread::yield_now();
                }
            }   
    }
    fn unlock(&self, id: usize){
        self.number[id].store(0, Ordering::SeqCst);
    }
}

fn main() {
    let bakery = Arc::new(Bakery::new());
    let mut handles = vec![];

    for id in 0..N {
        let bakery = Arc::clone(&bakery);
        let handle = thread::spawn(move || {
            
            for _ in 0..5 {
                bakery.lock(id);
                println!("thread {id} entered critical section");
                thread::sleep(Duration::from_millis(10));
                println!("thread {id} leaving critical section");
                
                bakery.unlock(id);
                thread::sleep(Duration::from_millis(5));
            }
        });
        handles.push(handle);
    }

    for handle in handles{
        handle.join().unwrap();
    }
}

