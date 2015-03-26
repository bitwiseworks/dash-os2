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
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>

/*
 * The cd and pwd commands.
 */

#include "shell.h"
#include "var.h"
#include "nodes.h"	/* for jobs.h */
#include "jobs.h"
#include "options.h"
#include "output.h"
#include "memalloc.h"
#include "error.h"
#include "exec.h"
#include "redir.h"
#include "main.h"
#include "mystring.h"
#include "show.h"
#include "cd.h"

#define CD_PHYSICAL 1
#define CD_PRINT 2

STATIC int docd(const char *, int);
STATIC const char *updatepwd(const char *);
STATIC char *getpwd(void);
STATIC int cdopt(void);

STATIC char *curdir = nullstr;		/* current working directory */
STATIC char *physdir = nullstr;		/* physical working directory */

STATIC int
cdopt()
{
	int flags = 0;
	int i, j;

	j = 'L';
	while ((i = nextopt("LP"))) {
		if (i != j) {
			flags ^= CD_PHYSICAL;
			j = i;
		}
	}

	return flags;
}

int
cdcmd(int argc, char **argv)
{
	const char *dest;
	const char *path;
	const char *p;
	char c;
	struct stat statb;
	int flags;

	flags = cdopt();
	dest = *argptr;
	if (!dest)
		dest = bltinlookup(homestr);
	else if (dest[0] == '-' && dest[1] == '\0') {
		dest = bltinlookup("OLDPWD");
		flags |= CD_PRINT;
	}
	if (!dest)
		dest = nullstr;
	if (PATH_IS_ABS_OR_ROOT(dest))
		goto step6;
	if (*dest == '.') {
		c = dest[1];
dotdot:
		switch (c) {
		case '\0':
		case '/':
#if PATH_USE_BACKSLASH
		case '\\':
#endif
			goto step6;
		case '.':
			c = dest[2];
			if (c != '.')
				goto dotdot;
		}
	}
	if (!*dest)
		dest = ".";
	path = bltinlookup("CDPATH");
	while (path) {
		c = *path;
		p = padvance(&path, dest);
		if (stat(p, &statb) >= 0 && S_ISDIR(statb.st_mode)) {
			if (c && c != PATH_SEP)
				flags |= CD_PRINT;
docd:
			if (!docd(p, flags))
				goto out;
			goto err;
		}
	}

step6:
	p = dest;
	goto docd;

err:
	sh_error("can't cd to %s", dest);
	/* NOTREACHED */
out:
	if (flags & CD_PRINT)
		out1fmt(snlfmt, curdir);
	return 0;
}


/*
 * Actually do the chdir.  We also call hashcd to let the routines in exec.c
 * know that the current directory has changed.
 */

STATIC int
docd(const char *dest, int flags)
{
	const char *dir = 0;
	int err;

	TRACE(("docd(\"%s\", %d) called\n", dest, flags));

	INTOFF;
	if (!(flags & CD_PHYSICAL)) {
		dir = updatepwd(dest);
		if (dir)
			dest = dir;
	}
	err = chdir(dest);
	TRACE(("chdir(\"%s\") returns %d\n", dest, err));
	if (err)
		goto out;
	setpwd(dir, 1);
	hashcd();
out:
	INTON;
	return err;
}


/*
 * Update curdir (the name of the current directory) in response to a
 * cd command.
 */

STATIC const char *
updatepwd(const char *dir)
{
	char *new;
	char *p;
	char *cdcomppath;
	const char *lim;

	cdcomppath = sstrdup(dir);
	STARTSTACKSTR(new);
	if (PATH_IS_REL(cdcomppath)) {
		if (curdir == nullstr)
			return 0;
#if PATH_USE_DRIVE
		if (PATH_IS_ROOT(cdcomppath)) {
			new = stnputs(curdir, PATH_ROOT_COMP_LEN(curdir), new);
			cdcomppath++;
			new = makestrspace(strlen(cdcomppath) + 1, new);
		} else
#endif
		{
			new = stputs(curdir, new);
			if (!PATH_IS_SLASH(new[-1]))
				USTPUTC('/', new);
			new = makestrspace(strlen(cdcomppath) + 1, new);
		}
		lim = stackblock();
		lim += PATH_ROOT_COMP_LEN(lim);
	} else {
		new = stnputs(cdcomppath, PATH_ROOT_COMP_LEN(cdcomppath), new);
		lim = stackblock();
		cdcomppath += (new - lim);
		lim += (new - lim);
		new = makestrspace(strlen(cdcomppath) + 1, new);
	}
#if PATH_USE_BACKSLASH
	for (p = stackblock(); p < new; p++) {
		if (*p == '\\')
			*p = '/';
	}
#endif
	p = strtok(cdcomppath, PATH_SLASHES);
	while (p) {
		switch(*p) {
		case '.':
			if (p[1] == '.' && p[2] == '\0') {
				while (new > lim) {
					STUNPUTC(new);
					if (PATH_IS_SLASH(new[-1]))
						break;
				}
				break;
			} else if (p[1] == '\0')
				break;
			/* fall through */
		default:
			new = stputs(p, new);
			USTPUTC('/', new);
		}
		p = strtok(0, PATH_SLASHES);
	}
	if (new > lim)
		STUNPUTC(new);
	*new = 0;
	return stackblock();
}


/*
 * Find out what the current directory is. If we already know the current
 * directory, this routine returns immediately.
 */
inline
STATIC char *
getpwd()
{
#ifdef __GLIBC__
	char *dir = getcwd(0, 0);

	if (dir)
		return dir;
#else
	char buf[PATH_MAX];

	if (getcwd(buf, sizeof(buf)))
		return savestr(buf);
#endif

	sh_warnx("getcwd() failed: %s", strerror(errno));
	return nullstr;
}

int
pwdcmd(int argc, char **argv)
{
	int flags;
	const char *dir = curdir;

	flags = cdopt();
	if (flags) {
		if (physdir == nullstr)
			setpwd(dir, 0);
		dir = physdir;
	}
	out1fmt(snlfmt, dir);
	return 0;
}

void
setpwd(const char *val, int setold)
{
	char *oldcur, *dir;

	oldcur = dir = curdir;

	if (setold) {
		setvar("OLDPWD", oldcur, VEXPORT);
	}
	INTOFF;
	if (physdir != nullstr) {
		if (physdir != oldcur)
			free(physdir);
		physdir = nullstr;
	}
	if (oldcur == val || !val) {
		char *s = getpwd();
		physdir = s;
		if (!val)
			dir = s;
	} else
		dir = savestr(val);
	if (oldcur != dir && oldcur != nullstr) {
		free(oldcur);
	}
	curdir = dir;
	INTON;
	setvar("PWD", dir, VEXPORT);
}
