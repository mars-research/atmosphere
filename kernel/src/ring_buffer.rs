#[repr(align(64))]
#[repr(C)]
pub struct RingBuffer<T, const N: usize> {
    pub head: usize,
    head_padding: [usize; 8],
    pub ar: [T; N],
    tail_padding: [usize; 8],
    pub tail: usize,
}

impl<const N: usize> RingBuffer<usize, N> {
    pub fn new() -> Self {
        Self {
            head: 0,
            head_padding: [0; 8],
            ar: [0; N],
            tail_padding: [0; 8],
            tail: 0,
        }
    }

    pub fn try_push(&mut self, target: usize) -> bool {
        if target == 0 {
            return false;
        }
        if self.ar[self.head] != 0 {
            return false;
        } else {
            self.ar[self.head] = target;
            if self.head == N - 1 {
                self.head = 0;
            } else {
                self.head = self.head + 1;
            }
            return true;
        }
    }

    pub fn try_pop(&mut self) -> Option<usize> {
        if self.ar[self.tail] == 0 {
            return None;
        } else {
            let ret = Some(self.ar[self.tail]);
            self.ar[self.tail] = 0;
            if self.tail == N - 1 {
                self.tail = 0;
            } else {
                self.tail = self.tail + 1;
            }
            return ret;
        }
    }
}
