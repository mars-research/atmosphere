pub const SIZE_OF_QUEUE:usize = 4096;
pub const SIZE_OF_BUFFER:usize = 8;

#[repr(align(4096))]
#[repr(C)]
pub struct DataBufferAllocWrapper{
    pub request_queue:RingBuffer::<usize,SIZE_OF_QUEUE>,
    pub reply_queue:RingBuffer::<usize,SIZE_OF_QUEUE>,
    pub free_stack:[usize;SIZE_OF_QUEUE],
    pub data_buffer:[[usize;SIZE_OF_BUFFER];SIZE_OF_QUEUE],
    pub len:usize,
}
impl DataBufferAllocWrapper{
    pub fn init(&mut self){
        self.request_queue.init();
        self.reply_queue.init();
        self.len = 0;
        for i in 0..SIZE_OF_QUEUE{
            for j in 0..SIZE_OF_BUFFER{
                self.data_buffer[i][j] = 0;
            }
        }
    }

    pub fn allocator_len(&self) -> usize{
        self.len
    }

    pub fn try_push_allocator(&mut self, value:usize) -> bool{
        if self.len < SIZE_OF_QUEUE{
            self.free_stack[self.len] = value;
            self.len += 1;
            true
        }else{
            false
        }
    }

    pub fn try_pop_allocator(&mut self) -> Option<usize>{
        if self.len > 0 {
            self.len -= 1;
            Some(self.free_stack[self.len])
        }else{
            None
        }
    }
}

#[repr(align(64))]
#[repr(C)]
pub struct RingBuffer<T,const N: usize>{
    pub head: usize,
    head_padding: [usize;8],
    pub ar: [T;N],
    tail_padding: [usize;8],
    pub tail: usize,
}

impl <const N: usize> RingBuffer<usize, N>{
    pub const fn new()-> Self{
        Self{
            head:0,
            head_padding:[0;8],
            ar:[usize::MAX;N],
            tail_padding:[0;8],
            tail:0,
        }
    }

    pub fn init(&mut self){
        self.head = 0;
        self.tail = 0;
        for i in 0..N{
            self.ar[i] = usize::MAX;
        }
    }

    pub fn try_push(&mut self, target:usize) -> bool{
        if target == usize::MAX{
            return false;
        }
        if self.ar[self.head] != usize::MAX{
            return false;
        }else{
            self.ar[self.head] = target;
            if self.head == N - 1{
                self.head = 0;
            }else{
                self.head = self.head + 1;
            }
            return true;
        }
    }

    pub fn try_pop(&mut self) -> Option<usize>{
        if self.ar[self.tail] == usize::MAX{
            return None;
        }else{
            let ret = Some(self.ar[self.tail]);
            self.ar[self.tail] = usize::MAX;
            if self.tail == N - 1{
                self.tail = 0;
            }else{
                self.tail = self.tail + 1;
            }
            return ret;
        }
    }
}
