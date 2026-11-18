/*
 * The C interface of the Atmosphere C runtime (atmo-rt).
 *
 * The runtime supplies the process entry point. It calls `int main(void)`
 * and ends the program with the value that main returns.
 *
 * Tasks are scheduled by strict priority. Priority 0 is the most urgent and
 * 255 the least. A task runs until it blocks, yields, or makes a more urgent
 * task ready. There is no time slicing. main() runs as a task of priority 0.
 *
 * Code that runs in the process must use general-purpose registers only; the
 * runtime does not save vector or floating-point state.
 */
#ifndef ATMO_RT_H
#define ATMO_RT_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Results. */
#define ART_OK         0
#define ART_TIMEOUT    1    /* the deadline passed, or a no-wait call would wait */
#define ART_FULL       2
#define ART_EMPTY      3
#define ART_ERROR      (-1)
#define ART_NOT_OWNER  (-2)
#define ART_TOO_LARGE  (-3)
#define ART_DESTROYED  (-4) /* the object was destroyed while the task waited */
#define ART_NO_MEMORY  (-5)

/* Deadlines are values of the monotonic clock in nanoseconds. */
#define ART_NO_WAIT    ((uint64_t)0)
#define ART_FOREVER    (UINT64_MAX)

#define ART_PRIORITY_MAX 0
#define ART_PRIORITY_MIN 255

/* ---- Console. Output is passed to the kernel one line at a time. ---- */
void art_console_write(const char *data, size_t len);
void art_console_flush(void);

/* Ends the program. Under QEMU the emulator exits with (code << 1) | 1. */
void art_exit(int code) __attribute__((noreturn));

/* The boot payload: the bytes that follow the image in the boot module.
 * *size is zero if there is none. */
const void *art_boot_payload(size_t *size);

/* ---- Clock ---- */
uint64_t art_clock_ns(void);          /* nanoseconds since start, monotonic */
uint64_t art_clock_counter_hz(void);  /* measured timestamp counter frequency */

/* The deadline that is `ns` nanoseconds from now. */
static inline uint64_t art_deadline_after(uint64_t ns)
{
    uint64_t now = art_clock_ns();
    return (ns > ART_FOREVER - 1 - now) ? ART_FOREVER - 1 : now + ns;
}

/* ---- Tasks ---- */
typedef uint32_t art_task_t;          /* zero is never a valid handle */
typedef void (*art_task_entry_t)(void *arg);

/* With a null stack the runtime maps one of at least stack_size bytes. A more
 * urgent new task runs before the call returns. */
int        art_task_create(art_task_t *task, art_task_entry_t entry, void *arg,
                           void *stack, size_t stack_size, uint8_t priority);
void       art_task_exit(void) __attribute__((noreturn));
int        art_task_delete(art_task_t task);
art_task_t art_task_self(void);
bool       art_task_valid(art_task_t task);
void       art_task_yield(void);
void       art_task_sleep(uint64_t ns);
void       art_task_sleep_until(uint64_t deadline);
int        art_task_set_priority(art_task_t task, uint8_t priority);
int        art_task_get_priority(art_task_t task, uint8_t *priority);
/* A value that the program attaches to a task. */
int        art_task_set_tag(art_task_t task, uintptr_t tag);
uintptr_t  art_task_get_tag(art_task_t task);
/* Lets the runtime notice deadlines that passed while a task computed. */
void       art_poll(void);

/* ---- Mutex: recursive, with priority inheritance ---- */
typedef struct art_mutex { uint64_t opaque[3]; } art_mutex_t;
void art_mutex_init(art_mutex_t *m);
int  art_mutex_lock(art_mutex_t *m);
int  art_mutex_unlock(art_mutex_t *m);
bool art_mutex_held(const art_mutex_t *m);
void art_mutex_destroy(art_mutex_t *m);

/* ---- Semaphore: counting, max = 1 makes it binary ---- */
typedef struct art_sem { uint64_t opaque[2]; } art_sem_t;
void     art_sem_init(art_sem_t *s, uint32_t initial, uint32_t max);
int      art_sem_take(art_sem_t *s, uint64_t deadline);
int      art_sem_give(art_sem_t *s);   /* ART_FULL at the maximum count */
int      art_sem_flush(art_sem_t *s);  /* releases all waiters, count unchanged */
uint32_t art_sem_count(const art_sem_t *s);
void     art_sem_destroy(art_sem_t *s);

/* ---- Message queue: bounded messages, put never waits ---- */
typedef struct art_queue { uint64_t opaque[5]; } art_queue_t;
int      art_queue_init(art_queue_t *q, uint32_t depth, uint32_t max_size);
int      art_queue_put(art_queue_t *q, const void *data, size_t size);
int      art_queue_get(art_queue_t *q, void *data, size_t capacity, size_t *size,
                       uint64_t deadline);
uint32_t art_queue_count(const art_queue_t *q);
void     art_queue_destroy(art_queue_t *q);

/* ---- Pages ---- */
#define ART_PAGE_SIZE 4096u
void *art_pages_alloc(size_t pages);          /* zeroed; NULL if out of memory */
void  art_pages_free(void *addr, size_t pages);

/* ---- In-memory file system ----
 * Paths are absolute. Calls return a negative ART_FS_E value on failure. */
#define ART_FS_READ      1u
#define ART_FS_WRITE     2u
#define ART_FS_CREATE    4u
#define ART_FS_TRUNCATE  8u

#define ART_FS_E_NOT_FOUND     (-2)
#define ART_FS_E_BAD_HANDLE    (-9)
#define ART_FS_E_NO_MEMORY     (-12)
#define ART_FS_E_ACCESS        (-13)
#define ART_FS_E_BUSY          (-16)
#define ART_FS_E_EXISTS        (-17)
#define ART_FS_E_NOT_DIR       (-20)
#define ART_FS_E_IS_DIR        (-21)
#define ART_FS_E_INVALID       (-22)
#define ART_FS_E_NO_SPACE      (-28)
#define ART_FS_E_NAME_TOO_LONG (-36)
#define ART_FS_E_NOT_EMPTY     (-39)

typedef struct art_fs_stat {
    uint64_t size;
    uint64_t mtime;  /* art_clock_ns() at the last change */
    uint32_t is_dir;
} art_fs_stat_t;

/* Registers data that is part of the image as a new read-only-backed file.
 * Missing parent directories are created. */
int     art_fs_add_static(const char *path, const void *data, size_t size);
/* Registers the regular files of a ustar archive, without copying them.
 * Returns the number of files. */
int     art_fs_add_tar(const void *data, size_t size);
int     art_fs_open(const char *path, uint32_t flags);       /* returns a handle */
int     art_fs_close(int fd);
int64_t art_fs_read(int fd, void *buf, size_t count);
int64_t art_fs_write(int fd, const void *buf, size_t count);
int64_t art_fs_seek(int fd, int64_t offset, uint32_t whence); /* 0 set, 1 current, 2 end */
int     art_fs_truncate(int fd, size_t size);
int     art_fs_stat(const char *path, art_fs_stat_t *out);
int     art_fs_remove(const char *path);
int     art_fs_rename(const char *from, const char *to);
int     art_fs_mkdir(const char *path, bool parents);
int     art_fs_rmdir(const char *path);
int     art_fs_clear(const char *path);                       /* removes all below path */
/* Returns 1 and an entry name, 0 at the end. *cursor starts at 0. */
int     art_fs_readdir(const char *path, uint32_t *cursor, char *name, size_t capacity);
int     art_fs_usage(const char *path, uint64_t *bytes, uint32_t *free_nodes);

#ifdef __cplusplus
}
#endif

#endif /* ATMO_RT_H */
