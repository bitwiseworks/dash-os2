/*-
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 * Copyright (c) 1997-2005
 *	Herbert Xu <herbert@gondor.apana.org.au>.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Kenneth Almquist.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)shell.h	8.2 (Berkeley) 5/4/95
 */

/*
 * The follow should be set to reflect the type of system you have:
 *	JOBS -> 1 if you have Berkeley job control, 0 otherwise.
 *	SHORTNAMES -> 1 if your linker cannot handle long names.
 *	define BSD if you are running 4.2 BSD or later.
 *	define SYSV if you are running under System V.
 *	define DEBUG=1 to compile in debugging ('set -o debug' to turn on)
 *	define DEBUG=2 to compile in and turn on debugging.
 *	define DO_SHAREDVFORK to indicate that vfork(2) shares its address
 *	       with its parent.
 *
 * When debugging is on, debugging info will be written to ./trace and
 * a quit signal will generate a core dump.
 */

#include <sys/param.h>
#ifdef __KLIBC__
#include <InnoTekLIBC/pathrewrite.h>
#endif

#ifndef JOBS
#define JOBS 1
#endif
#ifndef BSD
#define BSD 1
#endif

#ifndef DO_SHAREDVFORK
#if __NetBSD_Version__ >= 104000000
#define DO_SHAREDVFORK
#endif
#endif

#ifdef __OS2__
#define PATH_SEP ';'
#define PATH_SLASHES "\\/"
#define PATH_IS_SLASH(ch) ((ch) == '\\' || (ch) == '/')
#define PATH_USE_BACKSLASH 1
#define PATH_IS_UNC(path) \
    (PATH_IS_SLASH(*(path)) && PATH_IS_SLASH((path)[1]))
#define PATH_USE_DRIVE 1
#define PATH_IS_DRIVE(path) \
    (((*(path) >= 'A' && *(path) <= 'Z') || \
      (*(path) >= 'a' && *(path) <= 'z')) && (path)[1] == ':')
#define PATH_IS_DRIVE_ROOT(path) \
    (PATH_IS_DRIVE(path) && ((path)[2]=='\0' || PATH_IS_SLASH((path)[2])))
#ifdef __KLIBC__
#define PATH_IS_REWRITE(path) (__libc_PathRewrite((path), NULL, 0) > 0)
#else
#define PATH_IS_REWRITE(path) (0)
#endif
#define PATH_IS_ROOT(path) \
    (PATH_IS_SLASH(*(path)) && !PATH_IS_SLASH((path)[2]))
#define PATH_IS_ABS(path) (PATH_IS_UNC(path) || PATH_IS_DRIVE_ROOT(path) || PATH_IS_REWRITE(path))
#define PATH_IS_ABS_OR_ROOT(path) (PATH_IS_ABS(path) || PATH_IS_ROOT(path))
#define PATH_IS_REL(path) (!PATH_IS_ABS(path))
#define PATH_ROOT_COMP_LEN(path) \
    (PATH_IS_UNC(path) ? 2 : \
     PATH_IS_DRIVE(path) ? (PATH_IS_SLASH((path)[2]) ? 3 : 2) : \
     PATH_IS_ROOT(path) ? 1: 0)
#define PATH_HAS_SLASH(path) (strpbrk(path, PATH_SLASHES) != NULL)
#define EXE_USE_EXTS 1
#define EXE_EXTS_LIST ".exe", ".cmd", ".bat", ".com", ".btm"
#define EXE_EXTS_MAXLEN 4
#else
#define PATH_SEP ':'
#define PATH_SLASHES "/"
#define PATH_IS_SLASH(ch) ((ch) == '/')
#define PATH_USE_BACKSLASH 0
#define PATH_IS_UNC(path) (*(path) == '/' && (path)[1] == '/')
#define PATH_USE_DRIVE 0
#define PATH_IS_DRIVE(path) 0
#define PATH_IS_DRIVE_ROOT(path) 0
#define PATH_IS_ROOT(path) (*(path) == '/')
#define PATH_IS_ABS(path) (*(path) == '/')
#define PATH_IS_ABS_OR_ROOT(path) (*(path) == '/')
#define PATH_IS_REL(path) (*(path) != '/'))
#define PATH_ROOT_COMP_LEN(path) (*(path) == '/' ? 1 : 0)
#define PATH_HAS_SLASH(path) (strchr(path, '/') != NULL)
#define EXE_USE_EXTS 0
#define EXE_EXTS_LIST
#define EXE_EXTS_MAXLEN 0
#endif

#ifdef __OS2__
/* Limit process exit status to 0-255 for better *nix compatibility */
#ifdef __INNOTEK_LIBC__
#undef WEXITSTATUS
#define WEXITSTATUS(x) ((_W_INT(x) >> 8) & 0x000000ff)
#else
#error Port me!
#endif
#endif

typedef void *pointer;
#ifndef NULL
#define NULL (void *)0
#endif
#define STATIC static
#define MKINIT	/* empty */

extern char nullstr[1];		/* null string */


#ifdef DEBUG
#define TRACE(param)	trace param
#define TRACEV(param)	tracev param
#else
#define TRACE(param)
#define TRACEV(param)
#endif

#if defined(__GNUC__) && __GNUC__ < 3
#define va_copy __va_copy
#endif

#if !defined(__GNUC__) || (__GNUC__ == 2 && __GNUC_MINOR__ < 96)
#define __builtin_expect(x, expected_value) (x)
#endif

#define likely(x)	__builtin_expect(!!(x),1)
#define unlikely(x)	__builtin_expect(!!(x),0)

/*
 * Hack to calculate maximum length.
 * (length * 8 - 1) * log10(2) + 1 + 1 + 12
 * The second 1 is for the minus sign and the 12 is a safety margin.
 */
static inline int max_int_length(int bytes)
{
	return (bytes * 8 - 1) * 0.30102999566398119521 + 14;
}
