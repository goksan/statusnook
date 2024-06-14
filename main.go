package main

import (
	"bytes"
	"cmp"
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"database/sql"
	"embed"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"encoding/pem"
	"errors"
	"flag"
	"fmt"
	"html"
	"html/template"
	"io"
	"io/fs"
	"log"
	"math/big"
	mathRand "math/rand"
	"net"
	"net/http"
	"net/mail"
	"net/smtp"
	"net/url"
	"os"
	"os/signal"
	"path"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"syscall"
	textTemplate "text/template"
	"time"

	"github.com/caddyserver/certmagic"
	"github.com/go-chi/chi/v5"
	"github.com/go-chi/chi/v5/middleware"
	"github.com/mattn/go-sqlite3"
	"github.com/mholt/acmez/acme"
	"github.com/miekg/dns"
	"golang.org/x/crypto/bcrypt"
	"golang.org/x/mod/semver"
)

var BUILD = "dev"
var CA = certmagic.LetsEncryptStagingCA
var VERSION = "v0.2.0"

//go:embed schema.sql
var sqlSchema string

const SELF_SIGNED_CERT_NAME = "self-signed-cert.pem"
const SELF_SIGNED_KEY_NAME = "self-signed-key.pem"

func initDB(immediate bool) *sql.DB {
	if _, err := os.Stat("statusnook-data"); errors.Is(err, os.ErrNotExist) {
		err := os.Mkdir("statusnook-data", os.ModePerm)
		if err != nil {
			log.Fatalf("initDB.Mkdir: %s", err)
		}
	}

	dsn := "file:statusnook-data/app.db?_foreign_keys=on&_journal_mode=wal"
	if immediate {
		dsn += "&_txlock=immediate"
	}
	db, err := sql.Open("sqlite3", dsn)
	if err != nil {
		log.Fatalf("initDB.Open: %s", err)
	}

	if immediate {
		files, err := migrationsFS.ReadDir("migrations")
		if err != nil {
			log.Fatalf("initDB.ReadDir: %s", err)
		}

		slices.SortFunc(files, func(a, b fs.DirEntry) int {
			return cmp.Compare(a.Name(), b.Name())
		})

		const tableCountQuery = `
			select
				count(*)
			from
				sqlite_schema
			where 
				type = 'table' and 
				name not like 'sqlite_%';
		`

		tableCount := 0
		row := db.QueryRow(tableCountQuery)
		err = row.Scan(&tableCount)
		if err != nil {
			log.Fatalf("initDB.ScanTableCount: %s", err)
		}

		if tableCount == 0 {
			tx, err := db.Begin()
			if err != nil {
				log.Fatalf("initDB.BeginExecSchema: %s", err)
			}
			defer tx.Rollback()

			_, err = tx.Exec(sqlSchema)
			if err != nil {
				log.Fatalf("initDB.ExecSchema: %s", err)
			}

			params := []any{}
			placeholders := ""
			for i, v := range files {
				placeholders += "(?, ?)"
				if i < len(files)-1 {
					placeholders += ", "
				}
				params = append(params, strings.TrimRight(v.Name(), ".sql"), true)
			}

			insertMigrationQuery := fmt.Sprintf(
				`insert into migration(name, skipped) values %s;`,
				placeholders,
			)

			_, err = tx.Exec(insertMigrationQuery, params...)
			if err != nil {
				log.Fatalf("initDB.ExecInsertMigration: %s", err)
			}

			err = tx.Commit()
			if err != nil {
				log.Fatalf("initDB.CommitExecSchema: %s", err)
			}
		} else {
			const createMigrationTableQuery = `
				create table if not exists migration(
					id integer primary key,
					name text not null unique,
					skipped int not null
				);
			`

			_, err := db.Exec(createMigrationTableQuery)
			if err != nil {
				log.Fatalf("initDB.ExecCreateMigrationTable: %s", err)
			}

			existingMigrations := map[string]bool{}

			rows, err := db.Query("select name from migration")
			if err != nil {
				log.Fatalf("initDB.ExecQueryMigrations: %s", err)
			}
			defer rows.Close()

			for rows.Next() {
				var name string
				err = rows.Scan(&name)
				if err != nil {
					log.Fatalf("initDB.ScanMigration: %s", err)
				}

				existingMigrations[name] = true
			}

			for _, file := range files {
				migrationName := strings.TrimRight(file.Name(), ".sql")
				if _, ok := existingMigrations[migrationName]; ok {
					continue
				}

				data, err := migrationsFS.ReadFile(path.Join("migrations", file.Name()))
				if err != nil {
					log.Fatalf("initDB.ReadFile %s: %s", file.Name(), err)
				}

				func() {
					tx, err := db.Begin()
					if err != nil {
						log.Fatalf("initDB.BeginMigration %s: %s", file.Name(), err)
					}
					defer tx.Rollback()

					_, err = tx.Exec(string(data))
					if err != nil {
						log.Fatalf("initDB.ExecMigration %s: %s", file.Name(), err)
					}

					insertMigrationQuery := fmt.Sprintf(
						`insert into migration(name, skipped) values ('%s', false)`,
						migrationName,
					)
					_, err = tx.Exec(insertMigrationQuery)
					if err != nil {
						log.Fatalf("initDB.ExecInsertMigrationSkip %s: %s", file.Name(), err)
					}

					err = tx.Commit()
					if err != nil {
						log.Fatalf("initDB.CommitMigration %s: %s", file.Name(), err)
					}
				}()
			}
		}
	}

	return db
}

var tmpls = map[string]*template.Template{}

func parseTmpl(name string, markup string) (*template.Template, error) {
	if tmpl, ok := tmpls[name]; ok {
		return tmpl, nil
	}

	const rootTmpl = `
		<!DOCTYPE html>
		<html>
			<head>
				<title>{{template "title" .}}</title>
				<link rel="stylesheet" href="/static/main.css">
				<script type="text/javascript" src="/static/htmx.js"></script>
				<meta name="viewport" content="width=device-width, initial-scale=1" />
			</head>
			<body hx-history="false">
				<div class="root">
					<div class="page">
						{{if .Ctx.Status}}
							{{if and (not .Ctx.HideUnconfirmedDomain) (and .Ctx.Auth.ID .Ctx.UnconfirmedDomainProblem)}}
								<div class="banner">
									<span>
										<span class="title">Action required</span>: 
										issues acquiring certificate for '{{.Ctx.UnconfirmedDomain}}'
									</span>
									<a href="/admin/settings" hx-boost="true">
										click here for details
									</a>
								</div>
							{{end}}

							<div class="status-header">
								<div>
									<a id="nook-name" href="/" hx-boost="true">{{.Ctx.Name}}</a>
									{{if .Ctx.AdminArea}}
										<input id="nav-toggle" type="checkbox">
										<label for="nav-toggle">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
												<path fill-rule="evenodd" d="M2 4.75A.75.75 0 0 1 2.75 4h14.5a.75.75 0 0 1 0 1.5H2.75A.75.75 0 0 1 2 4.75ZM2 10a.75.75 0 0 1 .75-.75h14.5a.75.75 0 0 1 0 1.5H2.75A.75.75 0 0 1 2 10Zm0 5.25a.75.75 0 0 1 .75-.75h14.5a.75.75 0 0 1 0 1.5H2.75a.75.75 0 0 1-.75-.75Z" clip-rule="evenodd" />
											</svg>
										</label>
										<div class="nav nav--mobile">
											<a 
												href="/admin/alerts" 
												{{if eq .Ctx.Nav "alerts"}}class="active-nav"{{end}}
												hx-boost="true"
											>
												Alerts
											</a>
											<a 
												href="/admin/monitors" 
												{{if eq .Ctx.Nav "monitors"}}class="active-nav"{{end}}
												hx-boost="true"
											>
												Monitors
											</a>
											<a 
												href="/admin/services" 
												{{if eq .Ctx.Nav "services"}}class="active-nav"{{end}}
												hx-boost="true"
											>
												Services
											</a>										
											<a 
												href="/admin/notifications" 
												{{if eq .Ctx.Nav "notifications"}}class="active-nav"{{end}}
												hx-boost="true"
											>
												Notifications
											</a>

											<a 
												href="/admin/settings"
												{{if eq .Ctx.Nav "settings"}}class="active-nav"{{end}}
												hx-boost="true"
											>
												Settings
											</a>

											<a 
												href="/admin/update" 
												{{if eq .Ctx.Nav "update"}}class="active-nav"{{end}}
												hx-boost="true"
											>
												Update
											</a>

											<a hx-post="/logout">Log out</a>
										</div>
									{{end}}
								</div> 
								{{if .Ctx.Index}}
									<div>
										<div class="get-updates-container">
											{{if or .HasEmailAlertChannel .HasSlackSetup}}
												<button class="get-updates">
													<span>
														<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
															<path d="M3.105 2.288a.75.75 0 0 0-.826.95l1.414 4.926A1.5 1.5 0 0 0 5.135 9.25h6.115a.75.75 0 0 1 0 1.5H5.135a1.5 1.5 0 0 0-1.442 1.086l-1.414 4.926a.75.75 0 0 0 .826.95 28.897 28.897 0 0 0 15.293-7.155.75.75 0 0 0 0-1.114A28.897 28.897 0 0 0 3.105 2.288Z" />
														</svg>
														Get updates
													</span>
													<span></span>
												</button>
											{{end}}
										
											<dialog>
												{{if .HasEmailAlertChannel}}
													<button onclick="document.querySelector('.email-updates-modal').showModal();">
														<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
															<path d="M3 4a2 2 0 0 0-2 2v1.161l8.441 4.221a1.25 1.25 0 0 0 1.118 0L19 7.162V6a2 2 0 0 0-2-2H3Z" />
															<path d="m19 8.839-7.77 3.885a2.75 2.75 0 0 1-2.46 0L1 8.839V14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2V8.839Z" />
														</svg>
														Email
													</button>
												{{end}}
												{{if and .HasEmailAlertChannel .HasSlackSetup}}
													<hr>
												{{end}}
												{{if .HasSlackSetup}}
													<a href="{{.HasSlackSetup}}" target="_blank">
														<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
															<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
															<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
															<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
															<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
															<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
															<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
															<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
															<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
														</svg>
														Slack
													</a>
												{{end}}
											</dialog>
										</div>
										{{if and .Ctx.Index .Ctx.Auth.ID}}
											<a class="icon-button" href="/admin/alerts" hx-boost="true">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
													<path fill-rule="evenodd" d="M2.5 3A1.5 1.5 0 001 4.5v4A1.5 1.5 0 002.5 10h6A1.5 1.5 0 0010 8.5v-4A1.5 1.5 0 008.5 3h-6zm11 2A1.5 1.5 0 0012 6.5v7a1.5 1.5 0 001.5 1.5h4a1.5 1.5 0 001.5-1.5v-7A1.5 1.5 0 0017.5 5h-4zm-10 7A1.5 1.5 0 002 13.5v2A1.5 1.5 0 003.5 17h6a1.5 1.5 0 001.5-1.5v-2A1.5 1.5 0 009.5 12h-6z" clip-rule="evenodd" />
												</svg>
											</a>
										{{end}}
									</div>
								{{else if .Ctx.AdminArea}}
									<div class="nav">
										<a 
											href="/admin/alerts" 
											{{if eq .Ctx.Nav "alerts"}}class="active-nav"{{end}}
											hx-boost="true"
										>
											Alerts
										</a>
										<a 
											href="/admin/monitors" 
											{{if eq .Ctx.Nav "monitors"}}class="active-nav"{{end}}
											hx-boost="true"
										>
											Monitors
										</a>
										<a 
											href="/admin/services" 
											{{if eq .Ctx.Nav "services"}}class="active-nav"{{end}}
											hx-boost="true"
										>
											Services
										</a>										
										<a 
											href="/admin/notifications" 
											{{if eq .Ctx.Nav "notifications"}}class="active-nav"{{end}}
											hx-boost="true"
										>
											Notifications
										</a>

										<div id="nav-menu" class="menu" hx-preserve>
											<button class="menu-button">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
													<path fill-rule="evenodd" d="M4.22 6.22a.75.75 0 0 1 1.06 0L8 8.94l2.72-2.72a.75.75 0 1 1 1.06 1.06l-3.25 3.25a.75.75 0 0 1-1.06 0L4.22 7.28a.75.75 0 0 1 0-1.06Z" clip-rule="evenodd" />
												</svg>                                        
											</button>

											<dialog>
												<a href="/admin/settings" hx-boost="true">Settings</a>
												<a href="/admin/update" hx-boost="true">Update</a>
												<a hx-post="/logout">Log out</a>
											</dialog>
										</div>
									</div>
								{{end}}
							</div>
						{{end}}
						{{template "body" .}}
					</div>
				</div>

				<script>
					document.body.addEventListener("htmx:beforeSwap", function(evt) {
						if (!evt.detail.shouldSwap) {
							evt.detail.shouldSwap = evt.detail.xhr.status === 400;
						}
					});

					document.body.addEventListener("htmx:configRequest", function(evt) {
						evt.detail.headers["csrf-token"] = "{{.Ctx.Auth.CSRFToken}}";
					});


					function onClick(e) {
						if (!e.target.classList.contains("menu-button")) {
							[...document.querySelectorAll("dialog:not(.modal)")].forEach(e => {e.close();});
							document.removeEventListener("click", onClick);
						}
					}

					[...document.querySelectorAll(".menu-button")].forEach(function(e) {
						const menu = e.closest(".menu");
						if (menu.hasAttribute("hx-preserve")) {
							if (menu.dataset.preserve) {
								return;
							}
							menu.dataset.preserve = true;
						}

						e.addEventListener("click", function() {
							const options = menu.querySelector("dialog");
							if (!options.open) {
								[...document.querySelectorAll("dialog:not(.modal)")].forEach(e => {e.close();});
								options.show();
								document.addEventListener("click", onClick);
							} else {
								options.close();
							}
						});
					});

					{{if .Ctx.ShouldAttemptRedirect}}
						(async () => {
							const getResolveResponse = await fetch(
								"https://" + "{{.Ctx.Domain}}/resolve",
								{method: "GET"}
							);

							if (!getResolveResponse.ok || !getResolveResponse.headers.get("X-Statusnook")) {
								return;
							}

							const postResolveResponse = await fetch(
								window.location.origin + "/admin/resolve",
								{
									method: "POST",
									headers: {
										"csrf-token": "{{.Ctx.Auth.CSRFToken}}"
									}
								}
							);

							if (!postResolveResponse.ok) {
								return;
							}

							const token = await postResolveResponse.text();

							const params = new URLSearchParams({
								token, 
								after: window.location.pathname,
							});

							window.location.href = 
								"https://" + "{{.Ctx.Domain}}/cross-auth?" + params.toString();
						})();
					{{end}}
				</script>
			</body>
		</html>
	`

	tmpl, err := template.New(name).Parse(rootTmpl)
	if err != nil {
		return tmpl, err
	}

	tmpl, err = tmpl.Parse(markup)
	if err != nil {
		return tmpl, err
	}

	tmpls[name] = tmpl

	return tmpl, nil
}

var emailTmpls = map[string]*template.Template{}

func parseEmailTmpl(name string, markup string) (*template.Template, error) {
	if tmpl, ok := emailTmpls[name]; ok {
		return tmpl, nil
	}

	tmpl := template.New(name)

	tmpl, err := tmpl.Parse(markup)
	if err != nil {
		return tmpl, fmt.Errorf("parseEmailTmpl.Parse: %w", err)
	}

	emailTmpls[name] = tmpl

	return tmpl, nil
}

var textTmpls = map[string]*textTemplate.Template{}

func parseTextTmpl(name string, markup string) (*textTemplate.Template, error) {
	if tmpl, ok := textTmpls[name]; ok {
		return tmpl, nil
	}

	tmpl := textTemplate.New(name)

	tmpl, err := tmpl.Parse(markup)
	if err != nil {
		return tmpl, fmt.Errorf("parseTextTmpl.Parse: %w", err)
	}

	textTmpls[name] = tmpl

	return tmpl, nil
}

//go:embed static/*
var staticFS embed.FS

//go:embed migrations/*
var migrationsFS embed.FS

var appWg sync.WaitGroup
var db *sql.DB
var appCtx context.Context
var cancelAppCtx context.CancelFunc
var rwDB *sql.DB
var metaSetup string
var metaName string
var metaDomain string
var metaUnconfirmedDomain string
var metaUnconfirmedDomainProblem string
var metaSSL string

type statusCtxKey struct{}

type pageCtx struct {
	Status                   string
	Auth                     authCtx
	Index                    bool
	Name                     string
	HXRequest                bool
	HXBoosted                bool
	AdminArea                bool
	Nav                      string
	UnconfirmedDomainProblem string
	UnconfirmedDomain        string
	HideUnconfirmedDomain    bool
	ShouldAttemptRedirect    bool
	Domain                   string
}

func getPageCtx(r *http.Request) pageCtx {
	status := ""
	if val, ok := r.Context().Value(statusCtxKey{}).(string); ok {
		status = val
	}

	authCtx := getAuthCtx(r)

	adminURLPrefix := ""
	adminArea := false
	if strings.HasPrefix(r.URL.Path, "/admin/") {
		adminURLPrefix = strings.Split(r.URL.Path, "/")[2]
		adminArea = true
	}

	parsedURL, _ := url.ParseRequestURI("https://" + r.Host)

	return pageCtx{
		Status:                   status,
		Auth:                     authCtx,
		Index:                    r.URL.Path == "/" || r.URL.Path == "/history",
		Name:                     metaName,
		HXRequest:                r.Header.Get("HX-Request") == "true",
		HXBoosted:                r.Header.Get("HX-Boosted") == "true",
		AdminArea:                adminArea,
		Nav:                      adminURLPrefix,
		UnconfirmedDomainProblem: metaUnconfirmedDomainProblem,
		UnconfirmedDomain:        metaUnconfirmedDomain,
		HideUnconfirmedDomain:    r.URL.Path == "/admin/settings",
		ShouldAttemptRedirect: metaSSL == "true" && authCtx.ID != 0 &&
			metaDomain != "" && parsedURL.Hostname() != metaDomain,
		Domain: metaDomain,
	}
}

func csrfMiddleware(h http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method == http.MethodGet || r.Method == http.MethodHead || r.Method == http.MethodOptions {
			h.ServeHTTP(w, r)
			return
		}

		csrfToken := r.Header.Get("csrf-token")
		authCtx := getAuthCtx(r)

		if csrfToken != authCtx.CSRFToken {
			w.WriteHeader(http.StatusForbidden)
			return
		}

		h.ServeHTTP(w, r)
	})
}

func statusMiddleware(h http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		tx, err := db.Begin()
		if err != nil {
			log.Printf("statusMiddleware.Begin: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		severity, err := getSeverity(tx)
		if err != nil {
			tx.Rollback()
			log.Printf("statusMiddleware.getSeverity: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		if err = tx.Commit(); err != nil {
			log.Printf("statusMiddleware.Commit: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		ctx := context.WithValue(r.Context(), statusCtxKey{}, severity)

		h.ServeHTTP(w, r.WithContext(ctx))
	})
}

type authCtxKey struct{}

type authCtx struct {
	ID        int
	CSRFToken string
}

func getAuthCtx(r *http.Request) authCtx {
	ctx := authCtx{}
	if val, ok := r.Context().Value(authCtxKey{}).(authCtx); ok {
		ctx = val
	}

	return ctx
}

func createMonitorLog(
	tx *sql.Tx,
	startedAt time.Time,
	endedAt time.Time,
	responseCode int64,
	errorMessage sql.NullString,
	attempts int,
	result string,
	monitorID int,
) (int, error) {
	const query = `
		insert into 
			monitor_log(started_at, ended_at, response_code, error_message, 
				attempts, result, monitor_id)
			values(?, ?, ?, ?, ?, ?, ?)
		returning id
	`

	var id int

	err := tx.QueryRow(
		query,
		startedAt,
		endedAt,
		responseCode,
		errorMessage,
		attempts,
		result,
		monitorID,
	).Scan(&id)
	if err != nil {
		return id, fmt.Errorf("createMonitorLog.Exec: %w", err)
	}

	return id, nil
}

func createMonitorLogLastChecked(
	tx *sql.Tx,
	startedAt time.Time,
	monitorID int,
	monitorLogID int,
) error {
	const query = `
		insert into monitor_log_last_checked(checked_at, monitor_id, monitor_log_id)
			values(?, ?, ?) 
		on conflict(monitor_id) do update set 
			checked_at = excluded.checked_at,
			monitor_log_id = excluded.monitor_log_id
	`

	_, err := tx.Exec(
		query,
		startedAt,
		monitorID,
		monitorLogID,
		monitorLogID,
	)
	if err != nil {
		return fmt.Errorf("createMonitorLogLastChecked.Exec: %w", err)
	}

	return nil
}

type monitorLogLastChecked struct {
	ID           int
	CheckedAt    time.Time
	ResponseCode sql.NullInt32
}

func getMonitorLogLastChecked(
	tx *sql.Tx,
	monitorID int,
) (monitorLogLastChecked, error) {
	const query = `
		select monitor_log.monitor_id, checked_at, monitor_log.response_code 
		from monitor_log_last_checked
		left join monitor_log on monitor_log.id = monitor_log_last_checked.monitor_log_id
		where monitor_log_last_checked.monitor_id = ?
	`

	var lastChecked monitorLogLastChecked

	err := tx.QueryRow(query, monitorID).Scan(
		&lastChecked.ID,
		&lastChecked.CheckedAt,
		&lastChecked.ResponseCode,
	)
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			return lastChecked, nil
		}
		return lastChecked, fmt.Errorf("getMonitorLogLastChecked.QueryRow: %w", err)
	}

	return lastChecked, nil
}

func listAllMonitorLogLastChecked(tx *sql.Tx) ([]monitorLogLastChecked, error) {
	const query = `
		select monitor_log.monitor_id, checked_at, monitor_log.response_code 
		from monitor_log_last_checked
		left join monitor_log on monitor_log.id = monitor_log_last_checked.monitor_log_id
	`

	var allLastChecked []monitorLogLastChecked

	rows, err := tx.Query(query)
	if err != nil {
		return allLastChecked, fmt.Errorf("listAllMonitorLogLastChecked.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var lastChecked monitorLogLastChecked

		err := rows.Scan(
			&lastChecked.ID,
			&lastChecked.CheckedAt,
			&lastChecked.ResponseCode,
		)
		if err != nil {
			return allLastChecked, fmt.Errorf("listAllMonitorLogLastChecked.Scan: %w", err)
		}

		allLastChecked = append(allLastChecked, lastChecked)
	}

	return allLastChecked, nil
}

type plainOrLoginAuth struct {
	username string
	password string
	host     string
	auth     string
}

func PlainOrLoginAuth(username string, password string, host string) smtp.Auth {
	return &plainOrLoginAuth{username: username, password: password, host: host}
}

func (a *plainOrLoginAuth) Start(server *smtp.ServerInfo) (string, []byte, error) {
	if !server.TLS {
		return "", nil, fmt.Errorf("plainAuth.Start: unencrypted connection")
	}

	if slices.Contains(server.Auth, "PLAIN") {
		a.auth = "PLAIN"
		return smtp.PlainAuth("", a.username, a.password, a.host).Start(server)
	}

	if slices.Contains(server.Auth, "LOGIN") {
		a.auth = "LOGIN"
		return "LOGIN", []byte(a.username), nil
	}

	return "", nil, fmt.Errorf("plainAuth.Start: unhandled auth")
}

func (a *plainOrLoginAuth) Next(fromServer []byte, more bool) ([]byte, error) {
	if a.auth == "PLAIN" {
		return smtp.PlainAuth("", a.username, a.password, a.host).Next(fromServer, more)
	}

	if a.auth == "LOGIN" && more {
		switch string(fromServer) {
		case "Username:":
			return []byte(a.username), nil
		case "Password:":
			return []byte(a.password), nil
		default:
			return nil, fmt.Errorf("plainAuth.Next: unexpected from server")
		}
	}
	return nil, nil
}

func sendMonitorAlertEmail(
	monitor Monitor,
	channel NotificationChannel,
	statusCode sql.NullInt64,
	result string,
	startedAt time.Time,
	emailAddresses []string,
	status string,
) error {
	smtpDetail, ok := channel.Details.(SMTPNotificationDetails)
	if !ok {
		return fmt.Errorf(
			"sendMonitorAlertEmail.SMTPAssert: failed to assert channel %d",
			channel.ID,
		)
	}

	smtpAuth := PlainOrLoginAuth(
		smtpDetail.Username,
		smtpDetail.Password,
		smtpDetail.Host,
	)

	const downSubject = "🚨 Issue detected on monitor"
	const upSubject = "✅ Issue resolved on monitor"

	subject := downSubject
	if status == "up" {
		subject = upSubject
	}

	msg := [][]byte{
		[]byte("Subject: " + subject + " \"" +
			monitor.Name + "\""),
		[]byte("To: " + strings.Join(emailAddresses, ", ")),
		[]byte("From: " + metaName + " " + "<" + smtpDetail.From + ">"),
		[]byte("Content-Type: text/html; charset=UTF-8"),
	}
	for k, v := range smtpDetail.Headers {
		if strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") &&
			k == "X-PM-Message-Stream" {
			continue
		}
		msg = append(msg, []byte(k+": "+v))
	}
	if strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") {
		msg = append(msg, []byte("X-PM-Message-Stream: "+smtpDetail.Misc["pm-transactional"]))
	}

	const downMarkup = `
	{{- .MonitorName}} started failing<br><br>

	{{- if .StatusCode}}
		{{- "Status code"}}: {{.StatusCode}}<br>
	{{else}}
		{{- "Failure reason"}}: {{.Result}}<br>
	{{- end}}
	{{- "Checked at"}}: {{.CheckedAt}}<br><br>
	{{- ""}}<a href="https://{{.Domain}}/admin/monitors/{{.MonitorID}}">View monitor</a>
`

	const upMarkup = `
	{{- .MonitorName}} started succeeding<br><br>

	{{- "Checked at"}}: {{.CheckedAt}}<br><br>
	{{- ""}}<a href="https://{{.Domain}}/admin/monitors/{{.MonitorID}}">View monitor</a>
`

	markup := downMarkup
	if status == "up" {
		markup = upMarkup
	}

	tmpl, err := parseEmailTmpl(status+"MonitorSMTP", markup)
	if err != nil {
		return fmt.Errorf("sendMonitorAlertEmail.parseEmailTmplsSMTP: %w", err)
	}

	emailBytes := bytes.Buffer{}

	err = tmpl.Execute(
		&emailBytes,
		struct {
			MonitorID   int
			MonitorName string
			StatusCode  int
			CheckedAt   string
			Result      string
			Domain      string
		}{
			MonitorID:   monitor.ID,
			MonitorName: monitor.Name,
			StatusCode:  int(statusCode.Int64),
			CheckedAt:   startedAt.Format("2006/01/02 15:04:05 MST"),
			Result:      result,
			Domain:      metaDomain,
		},
	)
	if err != nil {
		return fmt.Errorf("sendMonitorAlertEmail.Execute: %w", err)
	}

	emailStr := "\r\n" + emailBytes.String()

	msg = append(msg, []byte(emailStr))

	err = smtp.SendMail(
		smtpDetail.Host+":"+strconv.Itoa(smtpDetail.Port),
		smtpAuth,
		smtpDetail.From,
		emailAddresses,
		bytes.Join(msg, []byte("\r\n")),
	)
	if err != nil {
		return fmt.Errorf("sendMonitorAlertEmail.SendMail: %w", err)
	}

	return nil
}

func sendMonitorAlertSlack(
	monitor Monitor,
	channel NotificationChannel,
	statusCode sql.NullInt64,
	startedAt time.Time,
	result string,
	httpClient http.Client,
	status string,
	domain string,
) error {
	slackDetail, ok := channel.Details.(SlackNotificationDetails)
	if !ok {
		return fmt.Errorf(
			"sendMonitorAlertSlack.SlackAssert: failed to assert channel %d",
			channel.ID,
		)
	}

	const downMarkup = `
		{{- ":rotating_light:"}} {{.MonitorName}} started failing{{"\n\n"}}

		{{- if .StatusCode}}
			{{- "Status code"}}: {{.StatusCode}}{{"\n"}}
		{{else}}
			{{- "Failure reason"}}: {{.Result}}{{"\n"}}
		{{- end}}
		{{- "Checked at"}}: {{.CheckedAt}}{{"\n\n"}}
		{{- ""}}<https://{{.Domain}}/admin/monitors/{{.MonitorID}}|View monitor>
	`

	const upMarkup = `
		{{- ":white_check_mark:"}} {{.MonitorName}} started succeeding{{"\n\n"}}

		{{- "Checked at"}}: {{.CheckedAt}}{{"\n\n"}}
		{{- ""}}<https://{{.Domain}}/admin/monitors/{{.MonitorID}}|View monitor>
	`

	markup := downMarkup
	if status == "up" {
		markup = upMarkup
	}

	tmpl, err := parseTextTmpl(status+"MonitorSlack", markup)
	if err != nil {
		return fmt.Errorf("sendMonitorAlertSlack.parseEmailTmplsSlack: %w", err)
	}

	emailStr := bytes.Buffer{}

	err = tmpl.Execute(
		&emailStr,
		struct {
			MonitorID   int
			MonitorName string
			StatusCode  int
			CheckedAt   string
			Result      string
			Domain      string
		}{
			MonitorID:   monitor.ID,
			MonitorName: monitor.Name,
			StatusCode:  int(statusCode.Int64),
			CheckedAt:   startedAt.Format("2006/01/02 15:04:05 MST"),
			Result:      result,
			Domain:      metaDomain,
		},
	)
	if err != nil {
		return fmt.Errorf("sendMonitorAlertSlack.Execute: %w", err)
	}

	type SlackWebhookRequestBody struct {
		Text string `json:"text"`
	}

	body := SlackWebhookRequestBody{Text: emailStr.String()}

	serializedBody, err := json.Marshal(body)
	if err != nil {
		return fmt.Errorf("sendMonitorAlertSlack.MarshalSlack: %w", err)
	}

	resp, err := httpClient.Post(
		slackDetail.WebhookURL,
		"application/json",
		bytes.NewBuffer(serializedBody),
	)
	if err != nil {
		return fmt.Errorf("sendMonitorAlertSlack.Post: %w", err)
	}
	resp.Body.Close()

	return nil
}

func monitorLoop(ctx context.Context, wg *sync.WaitGroup) {
	checkoutMu := sync.RWMutex{}
	lastCheckedMu := sync.RWMutex{}

	lastChecked := map[int]time.Time{}
	checkout := map[int]time.Time{}

	tick := time.Tick(time.Millisecond * 500)

	for {
		select {
		case <-tick:
			func() {
				tx, err := db.Begin()
				if err != nil {
					log.Printf("monitorLoop.BeginListMonitors: %s", err)
					return
				}
				defer tx.Rollback()

				monitors, err := listMonitors(tx)
				if err != nil {
					log.Printf("monitorLoop.listMonitors: %s", err)
					return
				}

				err = tx.Commit()
				if err != nil {
					log.Printf("monitorLoop.CommitListMonitors: %s", err)
					return
				}

				for _, monitor := range monitors {
					monitor := monitor

					httpClient := http.Client{
						Timeout: time.Duration(monitor.Timeout) * time.Second,
					}

					lastCheckedMu.RLock()
					if time.Since(lastChecked[monitor.ID]) <
						time.Second*time.Duration(monitor.Frequency) {
						lastCheckedMu.RUnlock()
						continue
					}
					lastCheckedMu.RUnlock()

					checkoutMu.RLock()
					if _, ok := checkout[monitor.ID]; ok {
						checkoutMu.RUnlock()
						return
					}
					checkoutMu.RUnlock()

					checkoutMu.Lock()
					checkout[monitor.ID] = time.Now().UTC()
					checkoutMu.Unlock()

					go func() {
						var endedAt time.Time

						defer func() {
							checkoutMu.Lock()
							delete(checkout, monitor.ID)
							checkoutMu.Unlock()

							if endedAt.IsZero() {
								endedAt = time.Now().UTC()
							}

							lastCheckedMu.Lock()
							lastChecked[monitor.ID] = endedAt
							lastCheckedMu.Unlock()
						}()

						startedAt := time.Now().UTC()

						var errorMessage sql.NullString

						var resp *http.Response
						var reqErr error
						var statusCode sql.NullInt64
						result := ""

						attempt := 0
						for attempt = 0; attempt < monitor.Attempts; attempt++ {
							var body io.Reader
							if monitor.Body.Valid {
								body = strings.NewReader(monitor.Body.String)
							}

							monitorReq, err := http.NewRequest(
								monitor.Method,
								monitor.URL,
								body,
							)
							if err != nil {
								log.Printf("monitorLoop.NewRequest: %s", err)
								break
							}
							for k, v := range monitor.RequestHeaders {
								monitorReq.Header.Add(k, v)
							}

							resp, reqErr = httpClient.Do(monitorReq)
							if reqErr != nil {
								continue
							}

							_, err = io.Copy(io.Discard, resp.Body)
							if err != nil {
								log.Printf("monitorLoop.Copy: %s", err)
								break
							}

							resp.Body.Close()

							statusCode = sql.NullInt64{
								Int64: int64(resp.StatusCode),
								Valid: true,
							}

							if resp.StatusCode >= 400 {
								result = "error"
								continue
							}

							result = "success"

							break
						}

						if result != "success" {
							urlErr := &url.Error{}
							if ok := errors.As(reqErr, &urlErr); ok {
								errorMessage = sql.NullString{
									String: reqErr.Error(),
									Valid:  true,
								}
								result = "timeout"
							}
						}

						endedAt = time.Now().UTC()

						tx, err := rwDB.Begin()
						if err != nil {
							log.Printf("monitorLoop.BeginMonitorLog: %s", err)
							return
						}
						defer tx.Rollback()

						monitorLogID, err := createMonitorLog(
							tx,
							startedAt,
							endedAt,
							statusCode.Int64,
							errorMessage,
							attempt,
							result,
							monitor.ID,
						)
						if err != nil {
							log.Printf("monitorLoop.createMonitorLog: %s", err)
							return
						}

						lastChecked, err := getMonitorLogLastChecked(tx, monitor.ID)
						if err != nil {
							log.Printf(
								"monitorLoop.checkNotificationDueByMonitorID: %s",
								err,
							)
							return
						}

						err = createMonitorLogLastChecked(tx, endedAt, monitor.ID, monitorLogID)
						if err != nil {
							log.Printf("monitorLoop.createMonitorLogLastChecked: %s", err)
							return
						}

						err = tx.Commit()
						if err != nil {
							log.Printf("monitorLoop.CommitMonitorLog: %s", err)
							return
						}

						tx, err = db.Begin()
						if err != nil {
							log.Printf("monitorLoop.BeginListNotificationsByMonitorID: %s", err)
							return
						}
						defer tx.Rollback()

						channels, err := listNotificationChannelsByMonitorID(tx, monitor.ID)
						if err != nil {
							log.Printf("monitorLoop.listNotificationChannelsByMonitorID: %s", err)
							return
						}

						err = tx.Commit()
						if err != nil {
							log.Printf("monitorLoop.CommitListNotificationChannelsByMonitorID: %s", err)
							return
						}

						if len(channels) > 0 {
							lastHappy := lastChecked.ResponseCode.Int32 != 0 &&
								lastChecked.ResponseCode.Int32 < 400

							if lastHappy && result != "success" || !lastHappy && result == "success" {
								status := "down"
								if result == "success" {
									status = "up"
								}

								tx, err = db.Begin()
								if err != nil {
									log.Printf("monitorLoop.BeginListMailGroupMembersEmailsByMonitorID: %s", err)
									return
								}
								defer tx.Rollback()

								emailAddresses, err := listMailGroupMembersEmailsByMonitorID(
									tx,
									monitor.ID,
								)
								if err != nil {
									log.Printf("monitorLoop.listMailGroupMembersEmailsByMonitorID: %s", err)
									return
								}

								err = tx.Commit()
								if err != nil {
									log.Printf("monitorLoop.CommitListMailGroupMembersEmailsByMonitorID: %s", err)
									tx.Rollback()
									return
								}

								skipEmail := len(emailAddresses) == 0

								for _, channel := range channels {
									if channel.Type == "smtp" && !skipEmail {
										err := sendMonitorAlertEmail(
											monitor,
											channel,
											statusCode,
											result,
											startedAt,
											emailAddresses,
											status,
										)
										if err != nil {
											log.Printf("monitorLoop.sendMonitorAlertEmail: %s", err)
											continue
										}
										skipEmail = true
									} else if channel.Type == "slack" {
										err = sendMonitorAlertSlack(
											monitor,
											channel,
											statusCode,
											startedAt,
											result,
											httpClient,
											status,
											metaDomain,
										)
										if err != nil {
											log.Printf("monitorLoop.sendMonitorAlertSlack: %s", err)
											continue
										}
									}
								}
							}
						}
					}()
				}
			}()
		case <-ctx.Done():
			wg.Done()
			return
		}
	}
}

type UnsentAlertNotification struct {
	AlertNotificationID int
	Destination         string
	Content             string
	Type                string
	AlertMessageID      int
	AlertTitle          string
	AlertType           string
	AlertSeverity       string
	AlertServices       string
}

func listUnsentAlertNotifications(tx *sql.Tx) ([]UnsentAlertNotification, error) {
	const query = `
		select 
			alert_notification.id, alert_subscription.destination, alert_message.content, 
			alert_subscription.type, alert_message.id, alert.title, alert.type, alert.severity, 
			group_concat(service.name, " • ")
		from alert_notification
		left join alert_subscription on alert_subscription.id = alert_subscription_id
		left join alert_message on alert_message.id = alert_message_id
		left join alert on alert.id = alert_message.alert_id
		left join alert_service on alert_service.alert_id = alert_message.alert_id
		left join service on service.id = alert_service.service_id
		where alert_notification.sent_at is null
		group by alert_notification.id
		order by alert_message.created_at asc
	`

	notifications := []UnsentAlertNotification{}

	rows, err := tx.Query(query)
	if err != nil {
		return notifications, fmt.Errorf("listUnsentAlertNotifications.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		notification := UnsentAlertNotification{}
		err := rows.Scan(
			&notification.AlertNotificationID,
			&notification.Destination,
			&notification.Content,
			&notification.Type,
			&notification.AlertMessageID,
			&notification.AlertTitle,
			&notification.AlertType,
			&notification.AlertSeverity,
			&notification.AlertServices,
		)
		if err != nil {
			return notifications, fmt.Errorf("listUnsentAlertNotifications.Scan: %w", err)
		}

		notifications = append(notifications, notification)
	}

	return notifications, nil
}

func notificationLoop(ctx context.Context, wg *sync.WaitGroup) {
	tick := time.Tick(time.Second * 10)
	for {
		select {
		case <-tick:
			func() {
				tx, err := db.Begin()
				if err != nil {
					log.Printf("notificationLoop.BeginListUnsentAlertNotifications: %s", err)
					return
				}
				defer tx.Rollback()

				notifications, err := listUnsentAlertNotifications(tx)
				if err != nil {
					log.Printf("notificationLoop.listUnsentAlertNotifications: %s", err)
					return
				}

				err = tx.Commit()
				if err != nil {
					log.Printf("notificationLoop.CommitListUnsentAlertNotifications: %s", err)
					return
				}

				for _, notification := range notifications {
					func() {
						tx, err := db.Begin()
						if err != nil {
							log.Printf("notificationLoop.ReadBegin: %s", err)
							return
						}
						defer tx.Rollback()

						notificationChannelID, err := getAlertSMTPNotificationSetting(tx)
						if err != nil {
							log.Printf("notificationLoop.getAlertSMTPNotificationSetting: %s", err)
							return
						}

						notificationChannel, err := getNotificationChannelByID(tx, notificationChannelID)
						if err != nil {
							log.Printf("notificationLoop.getNotificationChannelByID: %s", err)
							return
						}

						alertSettings, err := getAlertSettings(tx)
						if err != nil {
							log.Printf("notificationLoop.getAlertSettings: %s", err)
							return
						}

						emailSubs, err := listActiveAlertEmailSubscriptions(tx)
						if err != nil {
							log.Printf("notificationLoop.listActiveAlertEmailSubscriptions: %s", err)
							return
						}

						subTokensEmailMap := make(map[string]string, len(emailSubs))
						for _, v := range emailSubs {
							subTokensEmailMap[v.Destination] = v.Meta
						}

						err = tx.Commit()
						if err != nil {
							log.Printf("notificationLoop.ReadCommit: %s", err)
							return
						}

						severityEmoji := "🟠"
						if notification.AlertSeverity == "red" {
							severityEmoji = "🔴"
						}

						if notification.Type == "slack" {
							httpClient := http.Client{
								Timeout: time.Second * 10,
							}

							const text = `
								{
									"blocks": [
										{
											"type": "header",
											"text": {
												"type": "plain_text",
												"text": "{{.Title}}",
												"emoji": true
											}
										},
										{
											"type": "section",
											"text": {
												"type": "plain_text",
												"text": "{{.Content}}",
												"emoji": true
											}
										},
										{
											"type": "section",
											"fields": [
												{
													"type": "mrkdwn",
													"text": "*Affected services*\n{{.Services}}"
												},
												{{if eq .AlertType "incident"}}
												{
													"type": "mrkdwn",
													"text": "*Severity*\n{{.Severity}}"
												}
												{{end}}
											]
										},
										{
											"type": "section",
											"text": {
												"type": "mrkdwn",
												"text": "<https://{{.Domain}}|Visit status page>"
											}
										}
									]
								}
							`

							tmpl, err := parseTextTmpl("alertSlack", text)
							if err != nil {
								log.Printf("notificationLoop.parseEmailTmplsSlack: %s", err)
								return
							}

							notificationStr := bytes.Buffer{}

							err = tmpl.Execute(
								&notificationStr,
								struct {
									Title     string
									Content   string
									Services  string
									AlertType string
									Severity  string
									Domain    string
								}{
									Title: strings.ToUpper(notification.AlertType[:1]) +
										notification.AlertType[1:] + " - " + notification.AlertTitle,
									Content:   notification.Content,
									Services:  notification.AlertServices,
									AlertType: notification.AlertType,
									Severity:  severityEmoji,
									Domain:    metaDomain,
								},
							)
							if err != nil {
								log.Printf("notificationLoop.ExecuteSlack: %s", err)
								return
							}

							resp, err := httpClient.Post(
								notification.Destination,
								"application/json",
								&notificationStr,
							)
							if err != nil {
								log.Printf("notificationLoop.Post: %s", err)
								return
							}
							defer resp.Body.Close()

							tx, err := rwDB.Begin()
							if err != nil {
								log.Printf("notificationLoop.SlackBegin: %s", err)
								return
							}
							defer tx.Rollback()

							err = updateAlertSentAtByID(
								tx,
								time.Now().UTC(),
								[]int{notification.AlertNotificationID},
							)
							if err != nil {
								log.Printf("notificationLoop.updateAlertSentAtByID: %s", err)
								return
							}

							err = tx.Commit()
							if err != nil {
								log.Printf("notificationLoop.SlackCommit: %s", err)
								return
							}
						} else if notification.Type == "email" {
							smtpDetail, ok := notificationChannel.Details.(SMTPNotificationDetails)
							if !ok {
								log.Printf("notificationLoop.NotificationDetailsAssert: %s", err)
								return
							}

							msg := [][]byte{
								[]byte("Subject: " + metaName + " " + notification.AlertType +
									" alert: update regarding \"" + notification.AlertTitle + "\""),
								[]byte("To: " + notification.Destination),
								[]byte("From: " + metaName + " " + "<" + smtpDetail.From + ">"),
								[]byte("Content-Type: text/html; charset=UTF-8"),
							}
							for k, v := range smtpDetail.Headers {
								if strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") &&
									k == "X-PM-Message-Stream" {
									continue
								}
								msg = append(msg, []byte(k+": "+v))
							}
							if strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") {
								msg = append(
									msg,
									[]byte("X-PM-Message-Stream: "+smtpDetail.Misc["pm-broadcast"]),
								)
							}

							if alertSettings.ManagedSubscriptions {
								msg = append(
									msg,
									[]byte("List-Unsubscribe-Post: List-Unsubscribe=One-Click"),
									[]byte("List-Unsubscribe: "+
										"<https://"+metaDomain+
										"/unsubscribe?token="+subTokensEmailMap[notification.Destination]+">"),
								)
							}

							const markup = `The following message was posted for the alert "{{.Notification.AlertTitle}}":<br>
								{{- .Notification.Content}}<br><br>
							
								{{- "Affected services"}}: {{.Notification.AlertServices}}<br>
								{{if eq .Notification.AlertType "incident"}}
									{{- "Severity"}}: {{.SeverityEmoji}}<br>
								{{end}}
								<br>
								{{- ""}}<a href="https://{{.Domain}}">Visit status page</a>

								{{if .ManagedSubscriptions}}
									<br><br>
									<p style="text-align:center;margin:1em 0 3em">
										<a 
											href="https://{{.Domain}}/unsubscribe?token={{.SubToken}}"
											style="color:#a8aaaf;font-size:12px"
										>
											Unsubscribe
										</a>
									</p>
								{{end}}
							`

							tmpl, err := parseEmailTmpl("alert", markup)
							if err != nil {
								log.Printf("notificationLoop.parseEmailTmpls: %s", err)
								return
							}

							emailBytes := bytes.Buffer{}

							err = tmpl.Execute(
								&emailBytes,
								struct {
									Notification         UnsentAlertNotification
									SeverityEmoji        string
									Domain               string
									ManagedSubscriptions bool
									SubToken             string
								}{
									Notification:         notification,
									SeverityEmoji:        severityEmoji,
									Domain:               metaDomain,
									ManagedSubscriptions: alertSettings.ManagedSubscriptions,
									SubToken:             subTokensEmailMap[notification.Destination],
								},
							)
							if err != nil {
								log.Printf("notificationLoop.ExecuteSMTP: %s", err)
								return
							}

							emailStr := "\r\n" + emailBytes.String()

							msg = append(msg, []byte(emailStr))

							err = smtp.SendMail(
								smtpDetail.Host+":"+strconv.Itoa(smtpDetail.Port),
								PlainOrLoginAuth(
									smtpDetail.Username,
									smtpDetail.Password,
									smtpDetail.Host,
								),
								smtpDetail.From,
								[]string{notification.Destination},
								bytes.Join(msg, []byte("\r\n")),
							)
							if err != nil {
								log.Printf("notificationLoop.SendMail: %s", err)
								return
							}

							tx, err = rwDB.Begin()
							if err != nil {
								log.Printf("notificationLoop.BeginUpdateAlertSentAtByIDEmail: %s", err)
								return
							}
							defer tx.Rollback()

							err = updateAlertSentAtByID(
								tx,
								time.Now().UTC(),
								[]int{notification.AlertNotificationID},
							)
							if err != nil {
								log.Printf("notificationLoop.updateAlertSentAtByIDEmail: %s", err)
								return
							}

							err = tx.Commit()
							if err != nil {
								log.Printf("notificationLoop.CommitUpdateAlertSentAtByIDEmail: %s", err)
								return
							}
						}
					}()
				}
			}()
		case <-ctx.Done():
			wg.Done()
			return
		}
	}
}

func updateMetaValue(tx *sql.Tx, name string, value string) error {
	const query = `
		insert into meta(name, value) values(?, ?)
		on conflict(name) do update set value = excluded.value
	`

	_, err := tx.Exec(query, name, value)
	if err != nil {
		return fmt.Errorf("updateMetaValue.Exec: %w", err)
	}

	return nil
}

func getMetaValue(tx *sql.Tx, name string) (string, error) {
	const query = `
		select value from meta where name = ?
	`

	var v string

	err := tx.QueryRow(query, name).Scan(&v)
	if err != nil {
		return v, fmt.Errorf("getMetaValue.Scan: %w", err)
	}

	return v, nil
}

func neuter(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if strings.HasSuffix(r.URL.Path, "/") {
			http.NotFound(w, r)
			return
		}

		next.ServeHTTP(w, r)
	})
}

func attemptCertificateAcquisition(ctx context.Context, domain string) error {
	var testCache *certmagic.Cache
	testCache = certmagic.NewCache(certmagic.CacheOptions{
		GetConfigForCert: func(cert certmagic.Certificate) (*certmagic.Config, error) {
			return certmagic.New(testCache, certmagic.Config{}), nil
		},
	})
	testCache.Stop()

	testMagic := certmagic.New(testCache, certmagic.Config{})

	testACME := certmagic.NewACMEIssuer(testMagic, certmagic.ACMEIssuer{
		CA:     certmagic.LetsEncryptStagingCA,
		Email:  " ",
		Agreed: true,
	})

	testMagic.Issuers = []certmagic.Issuer{testACME}

	err := testMagic.ObtainCertSync(ctx, domain)
	if err != nil {
		return fmt.Errorf("attemptCertificateAcquisition.ObtainCertSync: %w", err)
	}

	fileStorage, ok := certmagic.Default.Storage.(*certmagic.FileStorage)
	if !ok {
		return fmt.Errorf("attemptCertificateAcquisition.FileStorageAssert: %w", err)
	}

	err = os.RemoveAll(
		fileStorage.Filename(certmagic.StorageKeys.CertsPrefix(testACME.IssuerKey())),
	)
	if err != nil {
		return fmt.Errorf("attemptCertificateAcquisition.RemoveAll: %w", err)
	}

	err = certmagic.ManageSync(ctx, []string{domain})
	if err != nil {
		return fmt.Errorf("attemptCertificateAcquisition.ManageSync: %w", err)
	}

	return nil
}

func monitorUnconfirmedDomainLoop(ctx context.Context, wg *sync.WaitGroup) {
	tick := time.Tick(time.Minute * 1)

	for {
		if metaUnconfirmedDomain == "" || metaUnconfirmedDomainProblem != "" {
			wg.Done()
			return
		}

		select {
		case <-tick:
			func() {
				found, err := lookupDomain(metaUnconfirmedDomain)
				if err != nil {
					log.Printf("monitorUnconfirmedDomainLoop.lookupDomain: %s", err)
					return
				}

				if !found {
					return
				}

				err = attemptCertificateAcquisition(ctx, metaUnconfirmedDomain)
				if err != nil {
					unconfirmedDomainProblemMsg := "An unexpected error occurred"

					var acmeProblem acme.Problem
					if errors.As(err, &acmeProblem) {
						var ok bool
						unconfirmedDomainProblemMsg, ok = acmeProblemTypeMessages[acmeProblem.Type]
						if !ok {
							unconfirmedDomainProblemMsg = "An unhandled error occurred " +
								acmeProblem.Type
						}
					} else {
						log.Printf("monitorUnconfirmedDomainLoop.attemptCertificateAcquisition: %s", err)
					}

					tx, err := rwDB.Begin()
					if err != nil {
						log.Printf("monitorUnconfirmedDomainLoop.BeginUnconfirmedDomainProblem: %s", err)
						return
					}
					defer tx.Rollback()

					metaUnconfirmedDomainProblem = unconfirmedDomainProblemMsg
					err = updateMetaValue(tx, "unconfirmedDomainProblem", metaUnconfirmedDomainProblem)
					if err != nil {
						log.Printf("monitorUnconfirmedDomainLoop.UpdateUnconfirmedDomainProblem: %s", err)
						return
					}

					if err := tx.Commit(); err != nil {
						log.Printf("monitorUnconfirmedDomainLoop.CommitUnconfirmedDomainProblem: %s", err)
						return
					}

					return
				}

				tx, err := rwDB.Begin()
				if err != nil {
					log.Printf("monitorUnconfirmedDomainLoop.Begin: %s", err)
					return
				}
				defer tx.Rollback()

				metaDomain = metaUnconfirmedDomain
				err = updateMetaValue(tx, "domain", metaUnconfirmedDomain)
				if err != nil {
					log.Printf("monitorUnconfirmedDomainLoop.updateMetaValueDomain: %s", err)
					return
				}

				metaUnconfirmedDomain = ""
				err = updateMetaValue(tx, "unconfirmedDomain", "")
				if err != nil {
					log.Printf("monitorUnconfirmedDomainLoop.updateMetaValueUnconfirmedDomain: %s", err)
					return
				}

				metaUnconfirmedDomainProblem = ""
				err = updateMetaValue(tx, "unconfirmedDomainProblem", "")
				if err != nil {
					log.Printf("monitorUnconfirmedDomainLoop.updateMetaValueUnconfirmedDomainProblem: %s", err)
					return
				}

				if err := tx.Commit(); err != nil {
					log.Printf("monitorUnconfirmedDomainLoop.Commit: %s", err)
					return
				}
			}()
		case <-ctx.Done():
			wg.Done()
			return
		}
	}
}

func GenerateSelfSignedCertificate() {
	priv, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		log.Fatalf("Failed to generate key: %v", err)
	}

	serialNumberLimit := new(big.Int).Lsh(big.NewInt(1), 128)
	serialNumber, err := rand.Int(rand.Reader, serialNumberLimit)
	if err != nil {
		log.Fatalf("Failed to generate serial number: %v", err)
	}

	notBefore := time.Now().UTC()
	notAfter := notBefore.Add(time.Hour * 720)

	template := x509.Certificate{
		SerialNumber: serialNumber,
		Subject: pkix.Name{
			Organization: []string{"Statusnook Installer"},
		},
		NotBefore:             notBefore,
		NotAfter:              notAfter,
		KeyUsage:              x509.KeyUsageDigitalSignature,
		ExtKeyUsage:           []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
		BasicConstraintsValid: true,
	}
	template.IsCA = true
	template.KeyUsage |= x509.KeyUsageCertSign

	derBytes, err := x509.CreateCertificate(rand.Reader, &template, &template, &priv.PublicKey, priv)
	if err != nil {
		log.Fatalf("Failed to create certificate: %v", err)
	}

	fingerprint := sha256.Sum256(derBytes)
	fingerprintHex := hex.EncodeToString(fingerprint[:])

	certFile, err := os.Create(SELF_SIGNED_CERT_NAME)
	if err != nil {
		log.Fatalf("Failed to open %s for writing: %v", SELF_SIGNED_CERT_NAME, err)
	}
	if err := pem.Encode(certFile, &pem.Block{Type: "CERTIFICATE", Bytes: derBytes}); err != nil {
		log.Fatalf("Failed to write data to %s: %v", SELF_SIGNED_CERT_NAME, err)
	}
	if err := certFile.Close(); err != nil {
		log.Fatalf("Error closing %s: %v", SELF_SIGNED_CERT_NAME, err)
	}

	keyOut, err := os.OpenFile(SELF_SIGNED_KEY_NAME, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0600)
	if err != nil {
		log.Fatalf("Failed to open %s for writing: %v", SELF_SIGNED_KEY_NAME, err)
	}
	privBytes, err := x509.MarshalPKCS8PrivateKey(priv)
	if err != nil {
		log.Fatalf("Unable to marshal private key: %v", err)
	}
	if err := pem.Encode(keyOut, &pem.Block{Type: "PRIVATE KEY", Bytes: privBytes}); err != nil {
		log.Fatalf("Failed to write data to %s: %v", SELF_SIGNED_KEY_NAME, err)
	}
	if err := keyOut.Close(); err != nil {
		log.Fatalf("Error closing %s: %v", SELF_SIGNED_KEY_NAME, err)
	}

	formattedFingerprint := ""
	for i := 0; i < len(fingerprintHex); i += 2 {
		formattedFingerprint +=
			strings.ToUpper(string(fingerprintHex[i])+string(fingerprintHex[i+1])) + ":"
	}
	formattedFingerprint = formattedFingerprint[:len(formattedFingerprint)-1]
	fmt.Println(formattedFingerprint)
}

var dockerFlag = flag.Bool("docker", false, "")

func main() {
	portFlag := flag.Int("port", 80, "")
	selfSignedFlag := flag.Bool("generate-self-signed-cert", false, "")

	flag.Parse()

	if *selfSignedFlag {
		GenerateSelfSignedCertificate()
		return
	}

	db = initDB(false)

	rwDB = initDB(true)
	rwDB.SetMaxOpenConns(1)

	tx, err := db.Begin()
	if err != nil {
		log.Fatalf("main.Begin: %s", err)
		return
	}
	defer tx.Rollback()

	setup, err := getMetaValue(tx, "setup")
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Fatalf("main.getMetaValueSetup: %s", err)
		return
	}
	metaSetup = setup

	name, err := getMetaValue(tx, "name")
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Fatalf("main.getMetaValueName: %s", err)
		return
	}
	metaName = name

	domain, err := getMetaValue(tx, "domain")
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Fatalf("main.getMetaValueDomain: %s", err)
		return
	}
	metaDomain = domain

	unconfirmedDomain, err := getMetaValue(tx, "unconfirmedDomain")
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Fatalf("main.getMetaValueUnconfirmedDomain: %s", err)
		return
	}
	metaUnconfirmedDomain = unconfirmedDomain

	unconfirmedDomainProblem, err := getMetaValue(tx, "unconfirmedDomainProblem")
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Fatalf("main.getMetaValueUnconfirmedDomainProblem: %s", err)
		return
	}
	metaUnconfirmedDomainProblem = unconfirmedDomainProblem

	ssl, err := getMetaValue(tx, "ssl")
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Fatalf("main.getMetaValueSSL: %s", err)
		return
	}
	if errors.Is(err, sql.ErrNoRows) {
		metaSSL = "true"
		if BUILD == "dev" || *portFlag != 80 {
			metaSSL = "false"
		}

		err = updateMetaValue(tx, "ssl", metaSSL)
		if err != nil {
			log.Printf("main.updateMetaValueSSL: %s", err)
			return
		}
	} else {
		metaSSL = ssl
	}

	err = tx.Commit()
	if err != nil {
		log.Fatalf("main.Commit: %s", err)
		return
	}

	r := chi.NewRouter()
	if BUILD == "dev" {
		r.Use(middleware.Logger)
	}
	if BUILD == "release" && metaSSL == "true" {
		r.Use(func(h http.Handler) http.Handler {
			return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				if certmagic.DefaultACME.HandleHTTPChallenge(w, r) {
					return
				}

				if r.TLS == nil {
					toURL := "https://"

					requestHost, _, err := net.SplitHostPort(r.Host)
					if err != nil {
						requestHost = r.Host
					}

					toURL += requestHost
					toURL += r.URL.RequestURI()

					w.Header().Set("Connection", "close")

					http.Redirect(w, r, toURL, http.StatusFound)

					return
				}
				h.ServeHTTP(w, r)
			})
		})
	}
	r.Use(func(h http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if metaSetup != "done" &&
				!strings.HasPrefix(r.URL.Path, "/setup") &&
				!strings.HasPrefix(r.URL.Path, "/static") {
				http.Redirect(w, r, "/setup", http.StatusFound)
				return
			}
			h.ServeHTTP(w, r)
		})
	})
	r.Use(func(h http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			tx, err := db.Begin()
			if err != nil {
				log.Printf("adminMiddleware.Begin: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				return
			}

			sessionToken, err := r.Cookie("session")
			if err != nil {
				tx.Rollback()
				h.ServeHTTP(w, r)
				return
			}

			id, csrfToken, err := validateSession(tx, sessionToken.Value)
			if err != nil {
				tx.Rollback()
				if !errors.Is(err, sql.ErrNoRows) {
					log.Printf("adminMiddleware.validateSession: %s", err)
					w.WriteHeader(http.StatusUnauthorized)
					return
				}
				h.ServeHTTP(w, r)
				return
			}

			if err = tx.Commit(); err != nil {
				log.Printf("adminMiddleware.Commit: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				return
			}

			ctx := context.WithValue(
				r.Context(),
				authCtxKey{},
				authCtx{
					ID:        id,
					CSRFToken: csrfToken,
				},
			)

			h.ServeHTTP(w, r.WithContext(ctx))
		})
	})

	fs := http.FileServer(http.FS(staticFS))
	r.Get("/static/*", neuter(fs).ServeHTTP)
	r.Route("/", func(r chi.Router) {
		r.Use(statusMiddleware)
		r.Get("/", index)
		r.Get("/resolve", getResolve)
		r.Get("/cross-auth", getCrossAuth)
		r.Get("/history", history)
		r.Get("/unsubscribe", getUnsubscribe)
		r.Post("/unsubscribe", postUnsubscribe)
		r.Post("/resubscribe", postResubscribe)
		r.Get("/invitation/{token}", getInvitation)
		r.Post("/invitation/{token}", postInvitation)
	})
	r.Route("/admin", func(r chi.Router) {
		r.Use(csrfMiddleware)
		r.Use(statusMiddleware)
		r.Use(func(h http.Handler) http.Handler {
			return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				ctx := getAuthCtx(r)

				if ctx.ID == 0 {
					http.Redirect(w, r, "/login", http.StatusFound)
					return
				}

				h.ServeHTTP(w, r)
			})
		})
		r.Get("/", adminIndex)
		r.Post("/resolve", postResolve)
		r.Route("/alerts", func(r chi.Router) {
			r.Get("/", alerts)
			r.Route("/notifications", func(r chi.Router) {
				r.Get("/", getAlertNotifications)
				r.Post("/", postAlertNotifications)
			})
			r.Get("/{id}", getAlert)
			r.Delete("/{id}", deleteAlert)
			r.Get("/create", getCreateAlert)
			r.Post("/create", postCreateAlert)
			r.Get("/{id}/edit", getEditAlert)
			r.Post("/{id}/edit", postEditAlert)
			r.Get("/{id}/messages", getAddAlertMessage)
			r.Post("/{id}/messages", postAddAlertMessage)
			r.Post("/{id}/resolve", postResolveAlert)
			r.Post("/{id}/unresolve", postUnresolveAlert)
			r.Delete("/{id}/messages/{messageID}", deleteAlertMessage)
			r.Get("/{id}/messages/{messageID}", getEditAlertMessage)
			r.Post("/{id}/messages/{messageID}", postEditAlertMessage)
		})
		r.Route("/monitors", func(r chi.Router) {
			r.Get("/", monitors)
			r.Get("/{id}", getMonitor)
			r.Get("/{id}/all", getMonitorAllLogs)
			r.Get("/{id}/poll", getMonitorPoll)
			r.Delete("/{id}", deleteMonitor)
			r.Get("/create", getCreateMonitor)
			r.Post("/create", postCreateMonitor)
			r.Get("/{id}/edit", getEditMonitor)
			r.Post("/{id}/edit", postEditMonitor)
		})
		r.Route("/services", func(r chi.Router) {
			r.Get("/", services)
			r.Get("/create", getCreateService)
			r.Post("/create", postCreateService)
			r.Delete("/{id}", deleteService)
			r.Get("/{id}/edit", getEditService)
			r.Post("/{id}/edit", postEditService)
		})
		r.Route("/notifications", func(r chi.Router) {
			r.Get("/", notifications)
			r.Get("/create", getCreateNotification)
			r.Post("/create", postCreateNotification)
			r.Delete("/{id}", deleteNotificationChannel)
			r.Get("/{id}/edit", getEditNotification)
			r.Post("/{id}/edit", postEditNotification)
			r.Route("/mail-groups", func(r chi.Router) {
				r.Get("/create", getCreateMailGroup)
				r.Post("/create", postCreateMailGroup)
				r.Get("/{id}/edit", getEditMailGroup)
				r.Post("/{id}/edit", postEditMailGroup)
				r.Delete("/{id}", deleteMailGroup)
			})
		})
		r.Route("/update", func(r chi.Router) {
			r.Get("/", update)
			r.Get("/check", updateCheck)
			r.Get("/after-update", afterUpdate)
			r.Post("/", postUpdate)
		})
		r.Route("/settings", func(r chi.Router) {
			r.Get("/", getSettings)
			r.Post("/", postSettings)
			r.Post("/cancel-domain", postSettingsCancelDomain)
			r.Get("/users/{id}/edit", getEditUser)
			r.Post("/users/{id}/edit", postEditUser)
			r.Delete("/users/{id}", deleteUser)
			r.Post("/users/invite", postInviteUser)
			r.Delete("/users/invite/{id}", postDeleteInvite)
		})
	})
	r.Route("/login", func(r chi.Router) {
		r.Get("/", getLogin)
		r.Post("/", postLogin)
	})
	r.Route("/logout", func(r chi.Router) {
		r.Use(csrfMiddleware)
		r.Post("/", logout)
	})
	r.Route("/setup", func(r chi.Router) {
		r.Use(func(h http.Handler) http.Handler {
			return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				tx, err := db.Begin()
				if err != nil {
					log.Printf("Setup.Begin: %s", err)
					return
				}
				defer tx.Rollback()

				v, err := getMetaValue(tx, "setup")
				if err != nil {
					log.Printf("Setup.getMetaValue: %s", err)
					return
				}

				err = tx.Commit()
				if err != nil {
					log.Printf("Setup.Commit: %s", err)
					return
				}

				if v == "done" {
					http.Redirect(w, r, "/", http.StatusFound)
					return
				}

				if r.URL.Path == "/setup/statusnook" {
					h.ServeHTTP(w, r)
					return
				}

				if v == "domain" && r.URL.Path == "/setup/skip-domain" {
					h.ServeHTTP(w, r)
					return
				}

				endpoints := map[string]string{
					"domain":  "/setup/domain",
					"account": "/setup/account",
					"name":    "/setup/name",
					"done":    "/",
				}

				url, ok := endpoints[v]
				if !ok {
					log.Printf("Setup.endpoints: no endpoint")
					return
				}

				if r.URL.Path == "/setup" || r.URL.Path != url {
					if r.Method == http.MethodGet {
						http.Redirect(w, r, url, http.StatusFound)
					} else {
						w.WriteHeader(http.StatusBadRequest)
					}
					return
				}

				h.ServeHTTP(w, r)
			})
		})
		r.Post("/statusnook", postSetupStatusnook)
		r.Options("/statusnook", postSetupStatusnook)
		r.Get("/domain", getSetupDomain)
		r.Post("/domain", postSetupDomain)
		r.Post("/skip-domain", postSetupDomainSkip)
		r.Get("/account", getSetupAccount)
		r.Post("/account", postSetupAccount)
		r.Get("/name", getSetupName)
		r.Post("/name", postSetupName)
	})
	r.Get("/callback/slack", slackOAuth2Callback)
	r.Post("/subscribe/email", postSubscribeEmail)
	r.Get("/subscribe/email/confirm", getSubscribeEmailConfirm)
	r.Post("/subscribe/email/confirm", postSubscribeEmailConfirm)
	r.Post("/test", func(w http.ResponseWriter, r *http.Request) {
		if r.Header.Get("aa") == "" {
			w.WriteHeader(http.StatusInternalServerError)
		}
	})

	appCtx, cancelAppCtx = context.WithCancel(context.Background())

	shutdownCh := make(chan os.Signal, 1)
	signal.Notify(shutdownCh, os.Interrupt, syscall.SIGTERM, syscall.SIGINT)

	appWg.Add(1)
	go monitorLoop(appCtx, &appWg)

	appWg.Add(1)
	go notificationLoop(appCtx, &appWg)

	var httpServer *http.Server
	var httpsServer *http.Server

	if BUILD == "dev" {
		httpLn, err := net.Listen("tcp", fmt.Sprintf(":%d", 8000))
		if err != nil {
			log.Fatalf("main.ListenHTTPS: %s", err)
		}

		httpServer = &http.Server{
			Handler:     r,
			BaseContext: func(listener net.Listener) context.Context { return appCtx },
		}

		go httpServer.Serve(httpLn)
	} else {
		host := ""
		if !*dockerFlag && *portFlag != 80 {
			host = "127.0.0.1"
		}

		httpLn, err := net.Listen("tcp", fmt.Sprintf("%s:%d", host, *portFlag))
		if err != nil {
			log.Fatalf("main.ListenHTTP: %s", err)
		}

		httpServer = &http.Server{
			ReadHeaderTimeout: 10 * time.Second,
			ReadTimeout:       30 * time.Second,
			WriteTimeout:      2 * time.Minute,
			IdleTimeout:       5 * time.Minute,
			Handler:           r,
			BaseContext:       func(listener net.Listener) context.Context { return appCtx },
		}

		go httpServer.Serve(httpLn)

		if metaSSL == "true" {
			certmagic.Default.Storage = &certmagic.FileStorage{Path: "certmagic"}
			certmagic.DefaultACME.Agreed = true
			certmagic.DefaultACME.CA = CA
			certmagic.DefaultACME.Email = " "

			domains := []string{}
			if domain != "" {
				domains = append(domains, metaDomain)
			}

			tlsConfig, err := certmagic.TLS(domains)
			if err != nil {
				log.Fatalf("main.TLS: %s", err)
			}
			tlsConfig.NextProtos = append([]string{"h2", "http/1.1"}, tlsConfig.NextProtos...)
			getCertificateCertMagic := tlsConfig.GetCertificate
			tlsConfig.GetCertificate = func(clientHello *tls.ClientHelloInfo) (*tls.Certificate, error) {
				certificate, err := getCertificateCertMagic(clientHello)
				if err != nil {
					certificate, err := tls.LoadX509KeyPair(
						SELF_SIGNED_CERT_NAME,
						SELF_SIGNED_KEY_NAME,
					)
					if err != nil {
						log.Printf("main.LoadX509KeyPair: %s", err)
						return &certificate, err
					}

					return &certificate, nil
				}

				return certificate, nil
			}

			httpsLn, err := tls.Listen("tcp", fmt.Sprintf(":%d", 443), tlsConfig)
			if err != nil {
				log.Fatalf("main.ListenHTTPS: %s", err)
			}

			httpsServer = &http.Server{
				ReadHeaderTimeout: 10 * time.Second,
				ReadTimeout:       30 * time.Second,
				WriteTimeout:      2 * time.Minute,
				IdleTimeout:       5 * time.Minute,
				Handler:           r,
				BaseContext:       func(listener net.Listener) context.Context { return appCtx },
			}

			go httpsServer.Serve(httpsLn)

			if unconfirmedDomain != "" && unconfirmedDomainProblem == "" {
				appWg.Add(1)
				go monitorUnconfirmedDomainLoop(appCtx, &appWg)
			}
		}
	}

	<-shutdownCh
	cancelAppCtx()
	appWg.Wait()

	if err := httpServer.Shutdown(context.Background()); err != nil {
		panic(err)
	}

	if httpsServer != nil {
		if err := httpsServer.Shutdown(context.Background()); err != nil {
			panic(err)
		}
	}

	err = db.Close()
	if err != nil {
		log.Printf("main.DBClose: %s", err)
	}

	err = rwDB.Close()
	if err != nil {
		log.Printf("main.rwDBClose: %s", err)
	}
}

type AlertSubscription struct {
	ID          int
	Type        string
	Destination string
	Meta        string
	Active      bool
}

func listActiveAlertEmailSubscriptions(tx *sql.Tx) ([]AlertSubscription, error) {
	const query = `
		select id, type, destination, meta, active from alert_subscription
		where type = 'email' and active = true
	`

	var subs []AlertSubscription

	rows, err := tx.Query(query)
	if err != nil {
		return subs, fmt.Errorf("listActiveAlertEmailSubscriptions.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var sub AlertSubscription

		err := rows.Scan(
			&sub.ID,
			&sub.Type,
			&sub.Destination,
			&sub.Meta,
			&sub.Active,
		)
		if err != nil {
			return subs, fmt.Errorf("listActiveAlertEmailSubscriptions.Scan: %w", err)
		}

		subs = append(subs, sub)
	}

	return subs, nil
}

func deleteAlertSubscriptionByMeta(tx *sql.Tx, meta string) error {
	const query = `
		delete from alert_subscription where meta = ?
	`

	_, err := tx.Exec(query, meta)
	if err != nil {
		return fmt.Errorf("deleteAlertSubscriptionByMeta.Exec: %w", err)
	}

	return nil
}

func updateEmailAlertSubscriptionActiveByMeta(tx *sql.Tx, meta string, active bool) error {
	const query = `
		update alert_subscription set active = ? where meta = ? and type = 'email'
	`

	_, err := tx.Exec(query, active, meta)
	if err != nil {
		return fmt.Errorf("updateEmailAlertSubscriptionActiveByMeta.Exec: %w", err)
	}

	return nil
}

func updateEmailAlertSubscriptionActiveByEmail(tx *sql.Tx, email string, active bool) error {
	const query = `
		update alert_subscription set active = ? where destination = ? and type = 'email'
	`

	_, err := tx.Exec(query, active, email)
	if err != nil {
		return fmt.Errorf("updateEmailAlertSubscriptionActiveByEmail.Exec: %w", err)
	}

	return nil
}

func createAlertSubscription(tx *sql.Tx, subscriptionType string, destination string, meta string) error {
	const query = `
		insert into alert_subscription(type, destination, meta) values(?, ?, nullif(?, ''))
		on conflict(type, destination) do update set active = true
	`

	_, err := tx.Exec(query, subscriptionType, destination, meta)
	if err != nil {
		return fmt.Errorf("createAlertSubscription.Exec: %w", err)
	}

	return nil
}

type SlackOAuthAccessResponse struct {
	OK   bool `json:"ok"`
	Team struct {
		ID string `json:"id"`
	} `json:"team"`
	IncomingWebhook struct {
		URL       string `json:"url"`
		ChannelID string `json:"channel_id"`
	} `json:"incoming_webhook"`
}

func slackOAuth2Callback(w http.ResponseWriter, r *http.Request) {
	code := r.URL.Query().Get("code")
	if code == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("slackOAuth2Callback.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	settings, err := getAlertSettings(tx)
	if err != nil {
		log.Printf("slackOAuth2Callback.getAlertSettings: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	slackInstallURL, err := url.ParseRequestURI(settings.SlackInstallURL)
	if err != nil {
		log.Printf("slackOAuth2Callback.ParseRequestURI: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	form := url.Values{}
	form.Add("code", code)
	form.Add("client_id", slackInstallURL.Query().Get("client_id"))
	form.Add("client_secret", settings.SlackClientSecret)

	resp, err := http.PostForm("https://slack.com/api/oauth.v2.access", form)
	if err != nil {
		log.Printf("slackOAuth2Callback.PostForm: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	respBody, err := io.ReadAll(resp.Body)
	if err != nil {
		log.Printf("slackOAuth2Callback.ReadAll: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	accessResponse := SlackOAuthAccessResponse{}

	err = json.Unmarshal(respBody, &accessResponse)
	if err != nil {
		log.Printf("slackOAuth2Callback.Unmarshal: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if !accessResponse.OK {
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	meta := accessResponse.Team.ID + "_" + accessResponse.IncomingWebhook.ChannelID

	err = deleteAlertSubscriptionByMeta(tx, meta)
	if err != nil {
		log.Printf("slackOAuth2Callback.deleteAlertSubscriptionByMeta: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = createAlertSubscription(
		tx,
		"slack",
		accessResponse.IncomingWebhook.URL,
		meta,
	)
	if err != nil {
		log.Printf("slackOAuth2Callback.createAlertSubscription: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("slackOAuth2Callback.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	http.Redirect(w, r, "/?slack_app_installed=1", http.StatusFound)
}

func postmarkDeleteSuppression(email string, token string, stream string) error {
	body := fmt.Sprintf(
		`
		{
			"Suppressions": [
				{
					"EmailAddress": "%s"
				}
			]
		}
		`,
		email,
	)

	httpClient := http.Client{
		Timeout: time.Second * 10,
	}

	req, err := http.NewRequest(
		http.MethodPost,
		"https://api.postmarkapp.com/message-streams/"+stream+"/suppressions/delete",
		strings.NewReader(body),
	)
	if err != nil {
		return fmt.Errorf("postmarkDeleteSuppression.NewRequest: %w", err)
	}

	req.Header.Add("Content-Type", "application/json")
	req.Header.Add("X-Postmark-Server-Token", token)

	resp, err := httpClient.Do(req)
	if err != nil {
		return fmt.Errorf("postmarkDeleteSuppression.Do: %w", err)
	}
	defer resp.Body.Close()

	respBody, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("postmarkDeleteSuppression.ReadAll: %w", err)
	}

	if resp.StatusCode != 200 {
		return fmt.Errorf("postmarkDeleteSuppression.StatusCode: %s", string(respBody))
	}

	return nil
}

func checkHasRecentPendingEmailAlertSubscription(tx *sql.Tx, email string, now time.Time) (bool, error) {
	const query = `
		select exists(
			select 1 from pending_email_alert_subscription where email = ?
			and created_at > datetime(?, '-10 minutes')
		)
	`

	var hasRecent bool

	err := tx.QueryRow(query, email, now).Scan(&hasRecent)
	if err != nil {
		return hasRecent, fmt.Errorf("checkHasRecentPendingEmailAlertSubscription.Exec: %w", err)
	}

	return hasRecent, nil
}

func createPendingEmailAlertSubscription(tx *sql.Tx, token string, email string, createdAt time.Time) error {
	const query = `
		insert into pending_email_alert_subscription(token, email, created_at)
		values(?, ?, ?)
	`

	_, err := tx.Exec(query, token, email, createdAt)
	if err != nil {
		return fmt.Errorf("createPendingEmailAlertSubscription.Exec: %w", err)
	}

	return nil
}

type SupressionDumpResponse struct {
	Suppressions []Supression
}

type Supression struct {
	EmailAddress      string
	SuppressionReason string
	Origin            string
	CreatedAt         time.Time
}

func postmarkDumpSupressions(token string, stream string) (SupressionDumpResponse, error) {
	httpClient := http.Client{
		Timeout: time.Second * 10,
	}

	var supressionsResp SupressionDumpResponse

	req, err := http.NewRequest(
		http.MethodGet,
		"https://api.postmarkapp.com/message-streams/"+stream+"/suppressions/dump"+
			"?SupressionReason=ManualSuppression",
		nil,
	)
	if err != nil {
		return supressionsResp, fmt.Errorf("postmarkDumpSupressions.NewRequest: %w", err)
	}

	req.Header.Add("Content-Type", "application/json")
	req.Header.Add("X-Postmark-Server-Token", token)

	resp, err := httpClient.Do(req)
	if err != nil {
		return supressionsResp, fmt.Errorf("postmarkDumpSupressions.Do: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return supressionsResp, fmt.Errorf("postmarkDumpSupressions.ReadAll: %w", err)
	}

	if resp.StatusCode != 200 {
		return supressionsResp, fmt.Errorf("postmarkDumpSupressions.StatusCode: %s", string(body))
	}

	err = json.Unmarshal(body, &supressionsResp)
	if err != nil {
		return supressionsResp, fmt.Errorf("postmarkDumpSupressions.Unmarshal: %w", err)
	}

	return supressionsResp, nil
}

var lastSuppressionSync time.Time
var supressionSyncMu sync.Mutex

func postSubscribeEmail(w http.ResponseWriter, r *http.Request) {
	email := r.PostFormValue("email")

	_, err := mail.ParseAddress(email)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	supressionSyncMu.Lock()
	if time.Since(lastSuppressionSync) > time.Second*10 {
		tx, err := db.Begin()
		if err != nil {
			supressionSyncMu.Unlock()
			log.Printf("postSubscribeEmail.BeginSuppressionsPrep: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
		defer tx.Rollback()

		alertNotificationChannelID, err := getAlertSMTPNotificationSetting(tx)
		if err != nil {
			supressionSyncMu.Unlock()
			log.Printf("postSubscribeEmail.getAlertSMTPNotificationSetting: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		notificationChannel, err := getNotificationChannelByID(tx, alertNotificationChannelID)
		if err != nil {
			supressionSyncMu.Unlock()
			log.Printf("postSubscribeEmail.getNotificationChannelByID: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		smtpDetail, ok := notificationChannel.Details.(SMTPNotificationDetails)
		if !ok {
			supressionSyncMu.Unlock()
			log.Printf("postSubscribeEmail.ChannelAssert: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		alertSettings, err := getAlertSettings(tx)
		if err != nil {
			supressionSyncMu.Unlock()
			log.Printf("postSubscribeEmail.getAlertSettings: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		err = tx.Commit()
		if err != nil {
			supressionSyncMu.Unlock()
			log.Printf("postSubscribeEmail.CommitBeginSuppressionsPrep: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		if !alertSettings.ManagedSubscriptions &&
			strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") {
			supressions, err := postmarkDumpSupressions(smtpDetail.Password, smtpDetail.Misc["pm-broadcast"])
			if err != nil {
				supressionSyncMu.Unlock()
				log.Printf("postSubscribeEmail.postmarkDumpSupressions: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				return
			}

			for _, v := range supressions.Suppressions {
				tx, err := rwDB.Begin()
				if err != nil {
					supressionSyncMu.Unlock()
					log.Printf("postSubscribeEmail.BeginSuppressions: %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					return
				}
				defer tx.Rollback()

				subscription, err := getAlertSubscriptionByEmail(tx, email)
				if err != nil {
					if !errors.Is(err, sql.ErrNoRows) {
						supressionSyncMu.Unlock()
						log.Printf("postSubscribeEmail.getAlertSubscriptionByEmail: %s", err)
						w.WriteHeader(http.StatusInternalServerError)
						return
					}
				}

				if subscription.ID != 0 {
					err = updateEmailAlertSubscriptionActiveByEmail(tx, v.EmailAddress, false)
					if err != nil {
						supressionSyncMu.Unlock()
						log.Printf(
							"postSubscribeEmail.updateEmailAlertSubscriptionActiveByEmail: %s",
							err,
						)
						w.WriteHeader(http.StatusInternalServerError)
						return
					}
				}

				err = tx.Commit()
				if err != nil {
					supressionSyncMu.Unlock()
					log.Printf("postSubscribeEmail.CommitSuppressions: %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					return
				}
			}
		}
		lastSuppressionSync = time.Now().UTC()
	}
	supressionSyncMu.Unlock()

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postSubscribeEmail.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	sub, err := getAlertSubscriptionByEmail(tx, email)
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Printf("postSubscribeEmail.getAlertSubscriptionByEmail: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if sub.Active {
		w.Write([]byte(`
		<dialog id="email-already-subscribed-modal" class="email-already-subscribed-modal success-modal" hx-swap-oob="true">
			<div>
				<div>
					<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
						<path fill-rule="evenodd" d="M16.704 4.153a.75.75 0 0 1 .143 1.052l-8 10.5a.75.75 0 0 1-1.127.075l-4.5-4.5a.75.75 0 0 1 1.06-1.06l3.894 3.893 7.48-9.817a.75.75 0 0 1 1.05-.143Z" clip-rule="evenodd" />
					</svg>
				</div>
				<span>
					This email address is already subscribed to receive updates
				</span>

				<button onclick="document.querySelector('.email-already-subscribed-modal').close();">Dismiss</button>
			</div>

			<script>
				document.querySelector('.email-updates-modal').close();
				document.querySelector('.email-already-subscribed-modal').showModal();
			</script>
		</dialog>
		`))
		return
	}

	const markup = `
		<dialog id="email-success-modal" class="email-success-modal success-modal" hx-swap-oob="true">
			<div>
				<div>
					<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
						<path fill-rule="evenodd" d="M16.704 4.153a.75.75 0 0 1 .143 1.052l-8 10.5a.75.75 0 0 1-1.127.075l-4.5-4.5a.75.75 0 0 1 1.06-1.06l3.894 3.893 7.48-9.817a.75.75 0 0 1 1.05-.143Z" clip-rule="evenodd" />
					</svg>
				</div>
				<span>
					To complete your subscription, click on the confirmation link which will arrive in your inbox
					in next few minutes
				</span>

				<button onclick="document.querySelector('.email-success-modal').close();">Dismiss</button>
			</div>

			<script>
				document.querySelector('.email-updates-modal').close();
				document.querySelector('.email-success-modal').showModal();
			</script>
		</dialog>
	`

	hasRecentPendingSub, err := checkHasRecentPendingEmailAlertSubscription(tx, email, time.Now().UTC())
	if err != nil {
		log.Printf("postSubscribeEmail.checkHasRecentPendingEmailAlertSubscription: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if hasRecentPendingSub {
		w.Write([]byte(markup))
		return
	}

	tokenBytes := make([]byte, 32)
	_, err = rand.Read(tokenBytes)
	if err != nil {
		log.Printf("postSubscribeEmail.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	token := base64.URLEncoding.EncodeToString(tokenBytes)

	err = createPendingEmailAlertSubscription(tx, token, email, time.Now().UTC())
	if err != nil {
		log.Printf("postSubscribeEmail.createPendingEmailAlertSubscription: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	notificationID, err := getAlertSMTPNotificationSetting(tx)
	if err != nil {
		log.Printf("postSubscribeEmail.getAlertSMTPNotificationSetting: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	channel, err := getNotificationChannelByID(tx, notificationID)
	if err != nil {
		log.Printf("postSubscribeEmail.getNotificationChannelByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	smtpDetail, ok := channel.Details.(SMTPNotificationDetails)
	if !ok {
		log.Printf("postSubscribeEmail.NotificationDetailsAssert: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	msg := [][]byte{
		[]byte("Subject: Confirm your subscription to " + metaName + " status alerts"),
		[]byte("To: " + email),
		[]byte("From: " + metaName + " " + "<" + smtpDetail.From + ">"),
		[]byte("Content-Type: text/html; charset=UTF-8"),
	}
	for k, v := range smtpDetail.Headers {
		if strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") &&
			k == "X-PM-Message-Stream" {
			continue
		}
		msg = append(msg, []byte(k+": "+v))
	}
	if strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") {
		msg = append(msg, []byte("X-PM-Message-Stream: "+smtpDetail.Misc["pm-transactional"]))
	}

	const emailTmpl = `Hi,<br><br>
	
To start receiving status alert emails from {{.Name}}, please <a href="{{.Link}}">confirm your subscription</a>.
<br><br>

If this email reached you by mistake, feel free to ignore it and we won't subscribe you.
`

	tmpl, err := parseEmailTmpl("alertConfirm", emailTmpl)
	if err != nil {
		log.Printf("postSubscribeEmail.parseEmailTmpls: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	protocol := "https"
	if BUILD == "dev" {
		protocol = "http"
	}

	emailBytes := bytes.Buffer{}

	err = tmpl.Execute(
		&emailBytes,
		struct {
			Name string
			Link string
		}{
			Name: metaName,
			Link: protocol + "://" + metaDomain + "/subscribe/email/confirm?token=" + token,
		},
	)
	if err != nil {
		log.Printf("postSubscribeEmail.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	emailStr := "\r\n" + emailBytes.String()

	msg = append(msg, []byte(emailStr))

	err = smtp.SendMail(
		smtpDetail.Host+":"+strconv.Itoa(smtpDetail.Port),
		PlainOrLoginAuth(
			smtpDetail.Username,
			smtpDetail.Password,
			smtpDetail.Host,
		),
		smtpDetail.From,
		[]string{email},
		bytes.Join(msg, []byte("\r\n")),
	)
	if err != nil {
		log.Printf("postSubscribeEmail.SendMail: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postSubscribeEmail.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Write([]byte(markup))
}

func updatePendingEmailAlertSubscription(tx *sql.Tx, confirmedAt time.Time, token string) error {
	const query = `
		update pending_email_alert_subscription set confirmed_at = ? where token = ?
	`

	_, err := tx.Exec(query, confirmedAt, token)
	if err != nil {
		return fmt.Errorf("updatePendingEmailAlertSubscription.Exec: %w", err)
	}

	return nil
}

func getAlertSubscriptionByEmail(tx *sql.Tx, email string) (AlertSubscription, error) {
	const query = `
		select id, type, destination, meta, active from alert_subscription
		where type = 'email' and destination = ?
	`

	var sub AlertSubscription
	err := tx.QueryRow(query, email).Scan(
		&sub.ID,
		&sub.Type,
		&sub.Destination,
		&sub.Meta,
		&sub.Active,
	)
	if err != nil {
		return sub, fmt.Errorf("getAlertSubscriptionByEmail.Scan: %w", err)
	}

	return sub, nil
}

func getPendingEmailAlertSubscriptionEmailByToken(tx *sql.Tx, token string) (string, error) {
	const query = `
		select email from pending_email_alert_subscription where token = ? and confirmed_at is null
	`

	var email string

	err := tx.QueryRow(query, token).Scan(&email)
	if err != nil {
		return email, fmt.Errorf("getPendingEmailAlertSubscriptionEmailByToken.Scan: %w", err)
	}

	return email, nil
}

func getSubscribeEmailConfirm(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Subscribe{{end}}
		{{define "body"}}
			<script>
				(async () => {
					const response = await fetch(
						window.location.href,
						{method: "POST"}
					);

					window.location.href = response.url;
				})();
			</script>		
		{{end}}
	`
	tmpl, err := parseTmpl("getSubscribeEmailConfirm", markup)
	if err != nil {
		log.Printf("getSubscribeEmailConfirm.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Ctx pageCtx
		}{
			Ctx: getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getSubscribeEmailConfirm.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postSubscribeEmailConfirm(w http.ResponseWriter, r *http.Request) {
	token := r.URL.Query().Get("token")
	if token == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.BeginRead: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	notificationChannelID, err := getAlertSMTPNotificationSetting(tx)
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.getAlertSMTPNotificationSetting: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	smtpNotificationChannel, err := getNotificationChannelByID(tx, notificationChannelID)
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.getNotificationChannelByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	email, err := getPendingEmailAlertSubscriptionEmailByToken(tx, token)
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.getPendingEmailAlertSubscriptionEmailByToken: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	sub, err := getAlertSubscriptionByEmail(tx, email)
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Printf("postSubscribeEmailConfirm.getAlertSubscriptionByEmail: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if sub.Active {
		return
	}

	smtpDetail, ok := smtpNotificationChannel.Details.(SMTPNotificationDetails)
	if !ok {
		log.Printf("postSubscribeEmailConfirm.Details: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alertSettings, err := getAlertSettings(tx)
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.getAlertSettings: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.CommitRead: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if !alertSettings.ManagedSubscriptions &&
		strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com") {
		err = postmarkDeleteSuppression(email, smtpDetail.Password, smtpDetail.Misc["pm-broadcast"])
		if err != nil {
			log.Printf("postSubscribeEmailConfirm.postmarkDeleteSuppression: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
	}

	tx, err = rwDB.Begin()
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.BeginUpdate: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updatePendingEmailAlertSubscription(tx, time.Now().UTC(), token)
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.updatePendingEmailAlertSubscription: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	tokenBytes := make([]byte, 32)
	_, err = rand.Read(tokenBytes)
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = createAlertSubscription(
		tx,
		"email",
		email,
		base64.URLEncoding.EncodeToString(tokenBytes),
	)
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.createAlertSubscription: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postSubscribeEmailConfirm.CommitUpdate: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	http.Redirect(w, r, "/?email_subscribed=1", http.StatusFound)
}

func getUnsubscribe(w http.ResponseWriter, r *http.Request) {
	token := r.URL.Query().Get("token")
	if token == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	const markup = `
		{{define "title"}}Unsubscribe{{end}}
		{{define "body"}}
			<form id="content" class="unsubscribe" hx-post hx-swap="none">
				<p>Please confirm you want to unsubscribe from alerts</p>
				<input name="token" type="hidden" value="{{.Token}}">
				<button>Unsubscribe</button>
			</form>			
		{{end}}
	`

	tmpl, err := parseTmpl("unsubscribe", markup)
	if err != nil {
		log.Printf("getUnsubscribeEmail.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Name  string
			Token string
			Ctx   pageCtx
		}{
			Name:  metaName,
			Token: token,
			Ctx:   getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getUnsubscribeEmail.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postUnsubscribe(w http.ResponseWriter, r *http.Request) {
	token := r.PostFormValue("token")
	if token == "" {
		token = r.URL.Query().Get("token")
	}

	if token == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postUnsubscribe.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updateEmailAlertSubscriptionActiveByMeta(tx, token, false)
	if err != nil {
		log.Printf("postUnsubscribe.updateEmailAlertSubscriptionActiveByMeta: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postUnsubscribe.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}You've been unsubscribed{{end}}
		{{define "body"}}
			<form id="content" class="unsubscribe" hx-post="/resubscribe" hx-swap="none" hx-swap-oob="true">
				<p>You've been unsubscribed</p>
				<input name="token" type="hidden" value="{{.Token}}">
				<button>Resubscribe</button>
			</form>			
		{{end}}
	`

	tmpl, err := parseTmpl("postUnsubscribe", markup)
	if err != nil {
		log.Printf("postUnsubscribe.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Name  string
			Token string
			Ctx   pageCtx
		}{
			Name:  metaName,
			Token: token,
			Ctx:   getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("postUnsubscribe.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postResubscribe(w http.ResponseWriter, r *http.Request) {
	token := r.PostFormValue("token")
	if token == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postResubscribe.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updateEmailAlertSubscriptionActiveByMeta(tx, token, true)
	if err != nil {
		log.Printf("postResubscribe.updateEmailAlertSubscriptionActiveByMeta: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postResubscribe.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}You've been re-subscribed{{end}}
		{{define "body"}}
			<div id="content" class="unsubscribe" hx-swap-oob="true">
				<p>You've been re-subscribed</p>
			</div>			
		{{end}}
	`

	tmpl, err := parseTmpl("postResubscribe", markup)
	if err != nil {
		log.Printf("postResubscribe.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Name  string
			Token string
			Ctx   pageCtx
		}{
			Name:  metaName,
			Token: token,
			Ctx:   getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("postResubscribe.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getInvitation(w http.ResponseWriter, r *http.Request) {
	inviteToken := chi.URLParam(r, "token")
	if inviteToken == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getInvitation.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	_, err = validateUserInvitationToken(tx, inviteToken, time.Now().UTC().Add(-time.Hour*24))
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		log.Printf("getInvitation.validateUserInvitationToken: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getInvitation.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}You're invited to create an admin user{{end}}
		{{define "body"}}
			<div class="auth-dialog-container">
				<div class="auth-dialog">
					<div>
						<div>
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path d="M10 8a3 3 0 100-6 3 3 0 000 6zM3.465 14.493a1.23 1.23 0 00.41 1.412A9.957 9.957 0 0010 18c2.31 0 4.438-.784 6.131-2.1.43-.333.604-.903.408-1.41a7.002 7.002 0 00-13.074.003z" />
					  		</svg>			
						</div>
						<h1>You're invited to create an admin user</h1>
					</div>
					<form hx-post hx-swap="none">
						<div id="alert" class="alert"></div>
						<label>
							Username
							<input name="username" required>
						</label>

						<label>
							Password
							<input name="password" type="password" required>
						</label>
					
						<label>
							Confirm password
							<input name="password-confirmation" type="password" required>
						</label>

						<button>Confirm</button>
					</form>
				</div>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getInvitation", markup)
	if err != nil {
		log.Printf("getInvitation.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(w, nil)
	if err != nil {
		log.Printf("getInvitation.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postInvitation(w http.ResponseWriter, r *http.Request) {
	inviteToken := chi.URLParam(r, "token")
	if inviteToken == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postInvitation.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	id, err := validateUserInvitationToken(tx, inviteToken, time.Now().UTC().Add(-time.Hour*24))
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		log.Printf("postInvitation.validateUserInvitationToken: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = deleteUserInvitation(tx, id)
	if err != nil {
		log.Printf("postInvitation.deleteUserInvitation: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	username := r.PostFormValue("username")
	if username == "" {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Username is required
			</div>
		`))
		return
	}

	password := r.PostFormValue("password")
	passwordConfirmation := r.PostFormValue("password-confirmation")

	if password != passwordConfirmation {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Passwords do not match
			</div>
		`))
		return
	}

	if len(password) < 8 {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Password must contain at least 8 characters
			</div>
		`))
		return
	}

	pwHash, err := bcrypt.GenerateFromPassword([]byte(password), bcrypt.DefaultCost)
	if err != nil {
		log.Printf("postInvitation.GenerateFromPassword: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	userID, err := createUser(tx, username, string(pwHash))
	if err != nil {
		var sqliteErr sqlite3.Error
		if errors.As(err, &sqliteErr) {
			if errors.Is(sqliteErr.Code, sqlite3.ErrConstraint) {
				w.WriteHeader(http.StatusBadRequest)
				w.Write([]byte(`
					<div id="alert" class="alert" hx-swap-oob="true">
						This username is already taken
					</div>
				`))
				return
			}
		}
		log.Printf("postInvitation.createUser: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	tokenBytes := make([]byte, 32)
	_, err = rand.Read(tokenBytes)
	if err != nil {
		log.Printf("postInvitation.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	csrfTokenBytes := make([]byte, 32)
	_, err = rand.Read(csrfTokenBytes)
	if err != nil {
		log.Printf("postInvitation.Read2: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	token := base64.StdEncoding.EncodeToString(tokenBytes)
	csrfToken := base64.StdEncoding.EncodeToString(csrfTokenBytes)

	err = createSession(tx, token, csrfToken, userID)
	if err != nil {
		log.Printf("postInvitation.createSession: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postInvitation.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	http.SetCookie(
		w,
		&http.Cookie{
			Name:     "session",
			Value:    token,
			Path:     "/",
			Expires:  time.Now().UTC().Add(time.Hour * 876600),
			Secure:   BUILD == "release",
			HttpOnly: true,
			SameSite: http.SameSiteLaxMode,
		},
	)

	w.Header().Add("HX-Location", "/admin/alerts")
}

func getOngoingAlerts(tx *sql.Tx) ([]AlertDetail, error) {
	const alertQuery = `
		select 
			id,
			title,
			type,
			severity,
			created_at,
			ended_at
		from
			alert
		where
			ended_at is null
		order by case 
			when severity = 'red' then 1
			when severity = 'amber' then 2
			else 3
		end asc
	`

	alerts := []AlertDetail{}

	rows, err := tx.Query(alertQuery)
	if err != nil {
		return alerts, fmt.Errorf("getOngoingAlerts.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		alert := AlertDetail{}
		err = rows.Scan(
			&alert.ID,
			&alert.Title,
			&alert.AlertType,
			&alert.Severity,
			&alert.CreatedAt,
			&alert.EndedAt,
		)
		if err != nil {
			return alerts, fmt.Errorf("getOngoingAlerts.Scan: %w", err)
		}

		alerts = append(alerts, alert)
	}

	alertIDs := make([]string, 0, len(alerts))
	for _, alert := range alerts {
		alertIDs = append(alertIDs, strconv.Itoa(alert.ID))
	}

	messageQuery := fmt.Sprintf(
		`
			select
				id,
				content,
				created_at,
				last_updated_at,
				alert_id
			from
				alert_message
			where
				alert_id in(%s)
			order by created_at desc
		`,
		strings.Join(alertIDs, ", "),
	)

	rows, err = tx.Query(messageQuery)
	if err != nil {
		return alerts, fmt.Errorf("getOngoingAlerts.Query2: %w", err)
	}
	defer rows.Close()

	messages := map[int][]AlertDetailMessage{}

	for rows.Next() {
		alertID := 0
		message := AlertDetailMessage{}
		err = rows.Scan(
			&message.ID,
			&message.Content,
			&message.CreatedAt,
			&message.LastUpdatedAt,
			&alertID,
		)
		if err != nil {
			return alerts, fmt.Errorf("getOngoingAlerts.Scan2: %w", err)
		}

		if _, ok := messages[alertID]; !ok {
			messages[alertID] = []AlertDetailMessage{}
		}
		messages[alertID] = append(messages[alertID], message)
	}

	serviceQuery := fmt.Sprintf(
		`
		select
			service.id,
			service.name,
			service.helper_text,
			alert_id
		from
			alert_service
		left join
			service on service.id = alert_service.service_id
		where
			alert_id in(%s)
		`,
		strings.Join(alertIDs, ", "),
	)

	rows, err = tx.Query(serviceQuery)
	if err != nil {
		return alerts, fmt.Errorf("getOngoingAlerts.Query3: %w", err)
	}
	defer rows.Close()

	services := map[int][]AlertDetailService{}

	for rows.Next() {
		alertID := 0

		service := AlertDetailService{}
		err = rows.Scan(
			&service.ID,
			&service.Name,
			&service.HelperText,
			&alertID,
		)
		if err != nil {
			return alerts, fmt.Errorf("getOngoingAlerts.Scan3: %w", err)
		}

		if _, ok := messages[alertID]; !ok {
			messages[alertID] = []AlertDetailMessage{}
		}
		services[alertID] = append(services[alertID], service)
	}

	for i, alert := range alerts {
		if _, ok := messages[alert.ID]; ok {
			alerts[i].Messages = messages[alert.ID]
		}
		if _, ok := services[alert.ID]; ok {
			alerts[i].Services = services[alert.ID]
		}
	}

	return alerts, nil
}

func index(w http.ResponseWriter, r *http.Request) {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("index.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	services, err := listServices(tx)
	if err != nil {
		log.Printf("index.listServices: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alerts, err := getOngoingAlerts(tx)
	if err != nil {
		log.Printf("index.getOngoingAlerts: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alertSettings, err := getAlertSettings(tx)
	if err != nil {
		log.Printf("index.getAlertSettings: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	hasSlackSetup := ""
	if alertSettings.SlackClientSecret != "" && alertSettings.SlackInstallURL != "" {
		hasSlackSetup = alertSettings.SlackInstallURL
	}

	emailAlertChannelID, err := getAlertSMTPNotificationSetting(tx)
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Printf("index.getAlertSMTPNotificationSetting: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	hasEmailAlertChannel := emailAlertChannelID != 0

	err = tx.Commit()
	if err != nil {
		log.Printf("index.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}{{.Ctx.Name}} Status{{end}}
		{{define "body"}}
			<div class="index-container">
				<div class="services-list">
					{{range $service := .Services}}
						<div class="service-row">
							<div>
								<span>{{$service.Name}}</span>
								<span>{{$service.HelperText}}</span>
							</div>
							<div>
								{{if eq (index $.ServiceStatuses $service.ID) "red"}}
									<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="#F84B37">
										<path stroke-linecap="round" stroke-linejoin="round" d="M12 9v3.75m9-.75a9 9 0 11-18 0 9 9 0 0118 0zm-9 3.75h.008v.008H12v-.008z" />
									</svg>
								{{else if eq (index $.ServiceStatuses $service.ID) "amber"}}
									<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="#E5B773" class="w-6 h-6">
  										<path stroke-linecap="round" stroke-linejoin="round" d="M12 9v3.75m-9.303 3.376c-.866 1.5.217 3.374 1.948 3.374h14.71c1.73 0 2.813-1.874 1.948-3.374L13.949 3.378c-.866-1.5-3.032-1.5-3.898 0L2.697 16.126zM12 15.75h.007v.008H12v-.008z" />
									</svg>
								{{else}}
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
										<path fill-rule="evenodd" d="M16.704 4.153a.75.75 0 01.143 1.052l-8 10.5a.75.75 0 01-1.127.075l-4.5-4.5a.75.75 0 011.06-1.06l3.894 3.893 7.48-9.817a.75.75 0 011.05-.143z" clip-rule="evenodd" />
									</svg>
								{{end}}
							</div>
						</div>
					{{end}}
				</div>

				{{if len .IncidentAlerts}}
					<div>
						<div class="index-alert-container">
							{{range $alert := .IncidentAlerts}}
								<div>
									<div>
										<div class="index-alert-container__header">
											<div>
												{{if eq $alert.Severity "red"}}
													<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="#F84B37">
														<path fill-rule="evenodd" d="M5.636 4.575a.75.75 0 0 1 0 1.061 9 9 0 0 0 0 12.728.75.75 0 1 1-1.06 1.06c-4.101-4.1-4.101-10.748 0-14.849a.75.75 0 0 1 1.06 0Zm12.728 0a.75.75 0 0 1 1.06 0c4.101 4.1 4.101 10.75 0 14.85a.75.75 0 1 1-1.06-1.061 9 9 0 0 0 0-12.728.75.75 0 0 1 0-1.06ZM7.757 6.697a.75.75 0 0 1 0 1.06 6 6 0 0 0 0 8.486.75.75 0 0 1-1.06 1.06 7.5 7.5 0 0 1 0-10.606.75.75 0 0 1 1.06 0Zm8.486 0a.75.75 0 0 1 1.06 0 7.5 7.5 0 0 1 0 10.606.75.75 0 0 1-1.06-1.06 6 6 0 0 0 0-8.486.75.75 0 0 1 0-1.06ZM9.879 8.818a.75.75 0 0 1 0 1.06 3 3 0 0 0 0 4.243.75.75 0 1 1-1.061 1.061 4.5 4.5 0 0 1 0-6.364.75.75 0 0 1 1.06 0Zm4.242 0a.75.75 0 0 1 1.061 0 4.5 4.5 0 0 1 0 6.364.75.75 0 0 1-1.06-1.06 3 3 0 0 0 0-4.243.75.75 0 0 1 0-1.061ZM10.875 12a1.125 1.125 0 1 1 2.25 0 1.125 1.125 0 0 1-2.25 0Z" clip-rule="evenodd" />
													</svg>
												{{else if eq $alert.Severity "amber"}}
													<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="#E5B773" class="w-6 h-6">
														<path stroke-linecap="round" stroke-linejoin="round" d="M12 9v3.75m-9.303 3.376c-.866 1.5.217 3.374 1.948 3.374h14.71c1.73 0 2.813-1.874 1.948-3.374L13.949 3.378c-.866-1.5-3.032-1.5-3.898 0L2.697 16.126zM12 15.75h.007v.008H12v-.008z" />
													</svg>
												{{else}}
													<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="#379BF8">
														<path stroke-linecap="round" stroke-linejoin="round" d="m11.25 11.25.041-.02a.75.75 0 0 1 1.063.852l-.708 2.836a.75.75 0 0 0 1.063.853l.041-.021M21 12a9 9 0 1 1-18 0 9 9 0 0 1 18 0Zm-9-3.75h.008v.008H12V8.25Z" />
													</svg>
												{{end}}
												<span>{{$alert.Title}}</span>
											</div>
											<span>{{$alert.Services}}</span>
										</div>
									</div>
									<div>
										{{range $message := $alert.Messages}}
											<div class="index-alert-container__row">
												<span>{{$message.CreatedAt}}</span>
												<span>{{$message.Content}}</span>
											</div>
										{{end}}
									</div>
								</div>
								<hr>
							{{end}}
						</div>
					</div>
				{{end}}

				
				
				<a class="index-link" href="/history" hx-boost="true">View full history</a>
				{{if not .Ctx.Auth.ID}}
					<a class="index-link index-link--secondary" href="/login" hx-boost="true">Manage this page</a>
				{{end}}

				<dialog class="email-updates-modal">
					<div>
						<span>Get email updates</span>
						<button onclick="document.querySelector('.email-updates-modal').close();">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path d="M6.28 5.22a.75.75 0 0 0-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 1 0 1.06 1.06L10 11.06l3.72 3.72a.75.75 0 1 0 1.06-1.06L11.06 10l3.72-3.72a.75.75 0 0 0-1.06-1.06L10 8.94 6.28 5.22Z" />
							</svg>
						</button>
					</div>
					<form hx-post="/subscribe/email" hx-swap="none">
						<label>
							Email address
							<input type="email" name="email" placeholder="example@example.com" required autofocus>
						</label>

						<button type="submit">Confirm</button>
					</form>
				</dialog>

				<dialog id="email-success-modal"></dialog>
				<dialog id="email-already-subscribed-modal"></dialog>

				<dialog class="slack-success-modal success-modal">
					<div>
						<div>
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M16.704 4.153a.75.75 0 0 1 .143 1.052l-8 10.5a.75.75 0 0 1-1.127.075l-4.5-4.5a.75.75 0 0 1 1.06-1.06l3.894 3.893 7.48-9.817a.75.75 0 0 1 1.05-.143Z" clip-rule="evenodd" />
							</svg>
						</div>
						<span>Updates will appear in Slack</span>

						<button onclick="document.querySelector('.slack-success-modal').close();">Dismiss</button>
					</div>
				</dialog>
				<dialog class="email-confirmation-success-modal success-modal">
					<div>
						<div>
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M16.704 4.153a.75.75 0 0 1 .143 1.052l-8 10.5a.75.75 0 0 1-1.127.075l-4.5-4.5a.75.75 0 0 1 1.06-1.06l3.894 3.893 7.48-9.817a.75.75 0 0 1 1.05-.143Z" clip-rule="evenodd" />
							</svg>
						</div>
						<span>You've successfully subscribed to receive updates via email</span>

						<button onclick="document.querySelector('.email-confirmation-success-modal').close();">Dismiss</button>
					</div>
				</dialog>

				<script>
					(() => {
						const query = new URLSearchParams(window.location.search);
						if (query.get("slack_app_installed")) {
							document.querySelector(".slack-success-modal").showModal();
							history.replaceState(null, "", "/");
						}
	
						if (query.get("email_subscribed")) {
							document.querySelector(".email-confirmation-success-modal").showModal();
							history.replaceState(null, "", "/");
						}	
					})();
				</script>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("index", markup)
	if err != nil {
		log.Printf("index.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	type FormattedAlertDetailMessage struct {
		ID            int
		Content       string
		CreatedAt     string
		LastUpdatedAt string
	}

	type FormattedAlertDetailService struct {
		ID         int
		Name       string
		HelperText string
	}

	type FormattedAlertDetail struct {
		ID        int
		Title     string
		AlertType string
		Severity  string
		CreatedAt string
		EndedAt   string
		Messages  []FormattedAlertDetailMessage
		Services  string
	}

	formattedAlerts := make([]FormattedAlertDetail, 0, len(alerts))

	for _, alert := range alerts {
		messages := make([]FormattedAlertDetailMessage, 0, len(alert.Messages))
		for _, message := range alert.Messages {
			createdAt := message.CreatedAt.Format("Jan 2 2006 • 15:04 MST")
			if message.CreatedAt.Year() == time.Now().UTC().Year() {
				createdAt = message.CreatedAt.Format("Jan 2 • 15:04 MST")
			}

			formattedMessage := FormattedAlertDetailMessage{
				ID:        message.ID,
				Content:   message.Content,
				CreatedAt: createdAt,
			}
			if message.LastUpdatedAt != nil {
				formattedMessage.LastUpdatedAt = message.LastUpdatedAt.Format(
					"02/01/2006 15:04",
				)
			}

			messages = append(messages, formattedMessage)
		}

		serviceNames := make([]string, 0, len(alert.Services))
		for _, service := range alert.Services {
			serviceNames = append(serviceNames, service.Name)
		}

		formattedAlert := FormattedAlertDetail{
			ID:        alert.ID,
			Title:     alert.Title,
			AlertType: alert.AlertType,
			Severity:  alert.Severity,
			CreatedAt: alert.CreatedAt.Format("02/01/2006 15:04 MST"),
			Messages:  messages,
			Services:  strings.Join(serviceNames, " • "),
		}
		if alert.EndedAt != nil {
			formattedAlert.EndedAt = alert.EndedAt.Format("02/01/2006 15:04 MST")
		}

		formattedAlerts = append(formattedAlerts, formattedAlert)
	}

	serviceStatuses := make(map[int]string, len(services))
	for _, service := range services {
		serviceStatuses[service.ID] = ""
	}
	for _, alert := range alerts {
		for _, service := range alert.Services {
			if serviceStatuses[service.ID] != "red" {
				serviceStatuses[service.ID] = alert.Severity
			}
		}
	}

	err = tmpl.Execute(
		w,
		struct {
			Services             []service
			IncidentAlerts       []FormattedAlertDetail
			ServiceStatuses      map[int]string
			HasEmailAlertChannel bool
			HasSlackSetup        string
			Ctx                  pageCtx
		}{
			Services:             services,
			IncidentAlerts:       formattedAlerts,
			ServiceStatuses:      serviceStatuses,
			HasEmailAlertChannel: hasEmailAlertChannel,
			HasSlackSetup:        hasSlackSetup,
			Ctx:                  getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("index.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getResolve(w http.ResponseWriter, r *http.Request) {
	w.Header().Add("X-Statusnook", "true")
	w.Header().Add("Access-Control-Allow-Origin", "*")
	w.Header().Add("Access-Control-Expose-Headers", "X-Statusnook")
}

var crossAuthTokens = map[string]int{}

func postResolve(w http.ResponseWriter, r *http.Request) {
	tokenBytes := make([]byte, 32)
	_, err := rand.Read(tokenBytes)
	if err != nil {
		log.Printf("postResolve.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	token := base64.URLEncoding.EncodeToString(tokenBytes)

	authCtx := getAuthCtx(r)
	crossAuthTokens[token] = authCtx.ID

	w.Write([]byte(token))
}

func getCrossAuth(w http.ResponseWriter, r *http.Request) {
	redirectURL := "https://" + metaDomain + r.URL.Query().Get("after")

	auth := getAuthCtx(r)
	if auth.ID != 0 {
		http.Redirect(w, r, redirectURL, http.StatusFound)
		return
	}

	tokenParam := r.URL.Query().Get("token")
	if tokenParam == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	userID, ok := crossAuthTokens[tokenParam]
	if !ok {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tokenBytes := make([]byte, 32)
	_, err := rand.Read(tokenBytes)
	if err != nil {
		log.Printf("getCrossAuth.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	csrfTokenBytes := make([]byte, 32)
	_, err = rand.Read(csrfTokenBytes)
	if err != nil {
		log.Printf("getCrossAuth.Read2: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	token := base64.StdEncoding.EncodeToString(tokenBytes)
	csrfToken := base64.StdEncoding.EncodeToString(csrfTokenBytes)

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("getCrossAuth.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	if err = createSession(tx, token, csrfToken, userID); err != nil {
		log.Printf("getCrossAuth.createSession: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("getCrossAuth.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	delete(crossAuthTokens, tokenParam)

	http.SetCookie(
		w,
		&http.Cookie{
			Name:     "session",
			Value:    token,
			Path:     "/",
			Expires:  time.Now().UTC().Add(time.Hour * 876600),
			Secure:   BUILD == "release",
			HttpOnly: true,
			SameSite: http.SameSiteLaxMode,
		},
	)

	http.Redirect(w, r, redirectURL, http.StatusFound)
}

func getOldestAlertDate(tx *sql.Tx) (time.Time, error) {
	const query = `
		select 
			created_at
		from
			alert
		order by 
			created_at asc
		limit 1
	`

	date := time.Time{}
	err := tx.QueryRow(query).Scan(&date)
	if err != nil {
		return date, fmt.Errorf("getOldestAlertDate: %w", err)
	}

	return date, nil
}

func getAlertHistory(tx *sql.Tx, period string) ([]AlertDetail, error) {
	const alertQuery = `
		select 
			id,
			title,
			type,
			severity,
			created_at,
			ended_at
		from
			alert
		where 
			strftime("%Y-%m", created_at) = ?
		order by created_at desc
	`

	alerts := []AlertDetail{}

	rows, err := tx.Query(alertQuery, period)
	if err != nil {
		return alerts, fmt.Errorf("getAlertHistory.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		alert := AlertDetail{}
		err = rows.Scan(
			&alert.ID,
			&alert.Title,
			&alert.AlertType,
			&alert.Severity,
			&alert.CreatedAt,
			&alert.EndedAt,
		)
		if err != nil {
			return alerts, fmt.Errorf("getAlertHistory.Scan: %w", err)
		}

		alerts = append(alerts, alert)
	}

	alertIDs := make([]string, 0, len(alerts))
	for _, alert := range alerts {
		alertIDs = append(alertIDs, strconv.Itoa(alert.ID))
	}

	messageQuery := fmt.Sprintf(
		`
			select
				id,
				content,
				created_at,
				last_updated_at,
				alert_id
			from
				alert_message
			where
				alert_id in(%s)
			order by created_at desc
		`,
		strings.Join(alertIDs, ", "),
	)

	rows, err = tx.Query(messageQuery)
	if err != nil {
		return alerts, fmt.Errorf("getAlertHistory.Query2: %w", err)
	}
	defer rows.Close()

	messages := map[int][]AlertDetailMessage{}

	for rows.Next() {
		alertID := 0
		message := AlertDetailMessage{}
		err = rows.Scan(
			&message.ID,
			&message.Content,
			&message.CreatedAt,
			&message.LastUpdatedAt,
			&alertID,
		)
		if err != nil {
			return alerts, fmt.Errorf("getAlertHistory.Scan2: %w", err)
		}

		if _, ok := messages[alertID]; !ok {
			messages[alertID] = []AlertDetailMessage{}
		}
		messages[alertID] = append(messages[alertID], message)
	}

	serviceQuery := fmt.Sprintf(
		`
		select
			service.id,
			service.name,
			service.helper_text,
			alert_id
		from
			alert_service
		left join
			service on service.id = alert_service.service_id
		where
			alert_id in(%s)
		`,
		strings.Join(alertIDs, ", "),
	)

	rows, err = tx.Query(serviceQuery)
	if err != nil {
		return alerts, fmt.Errorf("getAlertHistory.Query3: %w", err)
	}
	defer rows.Close()

	services := map[int][]AlertDetailService{}

	for rows.Next() {
		alertID := 0

		service := AlertDetailService{}
		err = rows.Scan(
			&service.ID,
			&service.Name,
			&service.HelperText,
			&alertID,
		)
		if err != nil {
			return alerts, fmt.Errorf("getAlertHistory.Scan3: %w", err)
		}

		if _, ok := messages[alertID]; !ok {
			messages[alertID] = []AlertDetailMessage{}
		}
		services[alertID] = append(services[alertID], service)
	}

	for i, alert := range alerts {
		if _, ok := messages[alert.ID]; ok {
			alerts[i].Messages = messages[alert.ID]
		}
		if _, ok := services[alert.ID]; ok {
			alerts[i].Services = services[alert.ID]
		}
	}

	return alerts, nil
}

func history(w http.ResponseWriter, r *http.Request) {
	periodParam := r.URL.Query().Get("period")

	if len(periodParam) == 0 {
		periodParam = time.Now().UTC().Format("2006-01")
	}

	if len(periodParam) != 7 {
		http.Redirect(w, r, "/history", http.StatusFound)
		return
	}

	periodDate, err := time.Parse("2006-01", periodParam)
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("history.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	oldestAlertDate, err := getOldestAlertDate(tx)
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Printf("history.getOldestAlertDate: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alerts, err := getAlertHistory(tx, periodParam)
	if err != nil {
		log.Printf("history.listAlerts: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	emailAlertChannelID, err := getAlertSMTPNotificationSetting(tx)
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Printf("history.getAlertSMTPNotificationSetting: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	hasEmailAlertChannel := emailAlertChannelID != 0

	alertSettings, err := getAlertSettings(tx)
	if err != nil {
		log.Printf("history.getAlertSettings: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	hasSlackSetup := ""
	if alertSettings.SlackClientSecret != "" && alertSettings.SlackInstallURL != "" {
		hasSlackSetup = alertSettings.SlackInstallURL
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("history.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Admin home{{end}}
		{{define "body"}}
			<div class="history-container">
				<div class="admin-nav-header">
					<div>
						<a href="/" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
						<h2>History</h2>
					</div>
					<div>
						<a {{if .PreviousPeriod}}href="/history?period={{.PreviousPeriod}}"{{end}} hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
								<path fill-rule="evenodd" d="M12.79 5.23a.75.75 0 01-.02 1.06L8.832 10l3.938 3.71a.75.75 0 11-1.04 1.08l-4.5-4.25a.75.75 0 010-1.08l4.5-4.25a.75.75 0 011.06.02z" clip-rule="evenodd" />
							</svg>
						</a>
						<span>{{.PeriodText}}</span>
						<a {{if .NextPeriod}}href="/history?period={{.NextPeriod}}"{{end}} hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
								<path fill-rule="evenodd" d="M7.21 14.77a.75.75 0 01.02-1.06L11.168 10 7.23 6.29a.75.75 0 111.04-1.08l4.5 4.25a.75.75 0 010 1.08l-4.5 4.25a.75.75 0 01-1.06-.02z" clip-rule="evenodd" />
							</svg>
						</a>
					</div>
				</div>
				{{if and (not (len .IncidentAlerts)) (not (len .MaintenanceAlerts))}}
					<div class="entity-empty-state">
						<div class="icon">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M8.485 2.495c.673-1.167 2.357-1.167 3.03 0l6.28 10.875c.673 1.167-.17 2.625-1.516 2.625H3.72c-1.347 0-2.189-1.458-1.515-2.625L8.485 2.495zM10 5a.75.75 0 01.75.75v3.5a.75.75 0 01-1.5 0v-3.5A.75.75 0 0110 5zm0 9a1 1 0 100-2 1 1 0 000 2z" clip-rule="evenodd" />
							</svg>
						</div>
						<span>No alerts for this period</span>
					</div>
				{{end}}
				{{if len .IncidentAlerts}}
					<div>
						<div class="index-alert-container">
							{{range $alert := .IncidentAlerts}}
								<div>
									<div>
										<div class="index-alert-container__header">
											<div>
												{{if eq $alert.Severity "red"}}
													<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="#F84B37">
														<path fill-rule="evenodd" d="M5.636 4.575a.75.75 0 0 1 0 1.061 9 9 0 0 0 0 12.728.75.75 0 1 1-1.06 1.06c-4.101-4.1-4.101-10.748 0-14.849a.75.75 0 0 1 1.06 0Zm12.728 0a.75.75 0 0 1 1.06 0c4.101 4.1 4.101 10.75 0 14.85a.75.75 0 1 1-1.06-1.061 9 9 0 0 0 0-12.728.75.75 0 0 1 0-1.06ZM7.757 6.697a.75.75 0 0 1 0 1.06 6 6 0 0 0 0 8.486.75.75 0 0 1-1.06 1.06 7.5 7.5 0 0 1 0-10.606.75.75 0 0 1 1.06 0Zm8.486 0a.75.75 0 0 1 1.06 0 7.5 7.5 0 0 1 0 10.606.75.75 0 0 1-1.06-1.06 6 6 0 0 0 0-8.486.75.75 0 0 1 0-1.06ZM9.879 8.818a.75.75 0 0 1 0 1.06 3 3 0 0 0 0 4.243.75.75 0 1 1-1.061 1.061 4.5 4.5 0 0 1 0-6.364.75.75 0 0 1 1.06 0Zm4.242 0a.75.75 0 0 1 1.061 0 4.5 4.5 0 0 1 0 6.364.75.75 0 0 1-1.06-1.06 3 3 0 0 0 0-4.243.75.75 0 0 1 0-1.061ZM10.875 12a1.125 1.125 0 1 1 2.25 0 1.125 1.125 0 0 1-2.25 0Z" clip-rule="evenodd" />
													</svg>
												{{else if eq $alert.Severity "amber"}}
													<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="#E5B773" class="w-6 h-6">
														<path stroke-linecap="round" stroke-linejoin="round" d="M12 9v3.75m-9.303 3.376c-.866 1.5.217 3.374 1.948 3.374h14.71c1.73 0 2.813-1.874 1.948-3.374L13.949 3.378c-.866-1.5-3.032-1.5-3.898 0L2.697 16.126zM12 15.75h.007v.008H12v-.008z" />
													</svg>
												{{else}}
													<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="#379BF8">
														<path stroke-linecap="round" stroke-linejoin="round" d="m11.25 11.25.041-.02a.75.75 0 0 1 1.063.852l-.708 2.836a.75.75 0 0 0 1.063.853l.041-.021M21 12a9 9 0 1 1-18 0 9 9 0 0 1 18 0Zm-9-3.75h.008v.008H12V8.25Z" />
													</svg>
												{{end}}
												<span>{{$alert.Title}}</span>
											</div>
											<span>{{$alert.Services}}</span>
										</div>
									</div>
									<div>
										{{range $message := $alert.Messages}}
											<div class="index-alert-container__row">
												<span>{{$message.CreatedAt}}</span>
												<span>{{$message.Content}}</span>
											</div>
										{{end}}
									</div>
								</div>
								<hr>
							{{end}}
						</div>
					</div>
				{{end}}

				<dialog class="email-updates-modal">
					<div>
						<span>Get email updates</span>
						<button onclick="document.querySelector('.email-updates-modal').close();">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path d="M6.28 5.22a.75.75 0 0 0-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 1 0 1.06 1.06L10 11.06l3.72 3.72a.75.75 0 1 0 1.06-1.06L11.06 10l3.72-3.72a.75.75 0 0 0-1.06-1.06L10 8.94 6.28 5.22Z" />
							</svg>
						</button>
					</div>
					<form hx-post="/subscribe/email" hx-swap="none">
						<label>
							Email address
							<input type="email" name="email" placeholder="example@example.com" required autofocus>
						</label>

						<button type="submit">Confirm</button>
					</form>
				</dialog>

				<dialog id="email-success-modal"></dialog>
				<dialog id="email-already-subscribed-modal"></dialog>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("history", markup)
	if err != nil {
		log.Printf("history.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	type FormattedAlertDetailMessage struct {
		ID            int
		Content       string
		CreatedAt     string
		LastUpdatedAt string
	}

	type FormattedAlertDetailService struct {
		ID         int
		Name       string
		HelperText string
	}

	type FormattedAlertDetail struct {
		ID        int
		Title     string
		AlertType string
		Severity  string
		CreatedAt string
		EndedAt   string
		Messages  []FormattedAlertDetailMessage
		Services  string
	}

	formattedAlerts := make([]FormattedAlertDetail, 0, len(alerts))

	for _, alert := range alerts {
		messages := make([]FormattedAlertDetailMessage, 0, len(alert.Messages))
		for _, message := range alert.Messages {
			formattedMessage := FormattedAlertDetailMessage{
				ID:        message.ID,
				Content:   message.Content,
				CreatedAt: message.CreatedAt.Format("Jan 2 • 15:04 MST"),
			}
			if message.LastUpdatedAt != nil {
				formattedMessage.LastUpdatedAt = message.LastUpdatedAt.Format(
					"02/01/2006 15:04 MST",
				)
			}

			messages = append(messages, formattedMessage)
		}

		serviceNames := make([]string, 0, len(alert.Services))
		for _, service := range alert.Services {
			serviceNames = append(serviceNames, service.Name)
		}

		formattedAlert := FormattedAlertDetail{
			ID:        alert.ID,
			Title:     alert.Title,
			AlertType: alert.AlertType,
			Severity:  alert.Severity,
			CreatedAt: alert.CreatedAt.Format("02/01/2006 15:04 MST"),
			Messages:  messages,
			Services:  strings.Join(serviceNames, " • "),
		}
		if alert.EndedAt != nil {
			formattedAlert.EndedAt = alert.EndedAt.Format("02/01/2006 15:04 MST")
		}

		formattedAlerts = append(formattedAlerts, formattedAlert)
	}

	previousPeriodDate := periodDate.AddDate(0, -1, 0)
	nextPeriodDate := periodDate.AddDate(0, 1, 0)

	previousPeriodStr := previousPeriodDate.Format("2006-01")
	nextPeriodStr := nextPeriodDate.Format("2006-01")

	now := time.Now().UTC()

	if oldestAlertDate.IsZero() ||
		time.Date(previousPeriodDate.Year(), previousPeriodDate.Month(), 1, 0, 0, 0, 0, now.Location()).
			Before(time.Date(oldestAlertDate.Year(), oldestAlertDate.Month(), 1, 0, 0, 0, 0, now.Location())) {
		previousPeriodStr = ""
	}

	if nextPeriodDate.After(time.Now().UTC()) {
		nextPeriodStr = ""
	}

	err = tmpl.Execute(
		w,
		struct {
			IncidentAlerts       []FormattedAlertDetail
			MaintenanceAlerts    []FormattedAlertDetail
			PeriodText           string
			PreviousPeriod       string
			NextPeriod           string
			HasEmailAlertChannel bool
			HasSlackSetup        string
			Ctx                  pageCtx
		}{
			IncidentAlerts:       formattedAlerts,
			PeriodText:           periodDate.Format("Jan 2006"),
			PreviousPeriod:       previousPeriodStr,
			NextPeriod:           nextPeriodStr,
			HasEmailAlertChannel: hasEmailAlertChannel,
			HasSlackSetup:        hasSlackSetup,
			Ctx:                  getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("history.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getLogin(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Log in{{end}}
		{{define "body"}}
			<div class="auth-dialog-container">
				<div class="auth-dialog">
					<div>
						<div>
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M8 7a5 5 0 113.61 4.804l-1.903 1.903A1 1 0 019 14H8v1a1 1 0 01-1 1H6v1a1 1 0 01-1 1H3a1 1 0 01-1-1v-2a1 1 0 01.293-.707L8.196 8.39A5.002 5.002 0 018 7zm5-3a.75.75 0 000 1.5A1.5 1.5 0 0114.5 7 .75.75 0 0016 7a3 3 0 00-3-3z" clip-rule="evenodd" />
					  		</svg>	  
						</div>
						<h1>Log in</h1>
					</div>
					<form hx-post hx-swap="none">
						<div id="alert" class="alert" hx-swap-oob></div>
						<label>
							Username
							<input name="username" required />
						</label>

						<label>
							Password
							<input name="password" type="password" required/>
						</label>

						<button>Confirm</button>
					</form>
				</div>
			</div>
		{{end}}
	`

	authCtx := getAuthCtx(r)
	if authCtx.ID != 0 {
		http.Redirect(w, r, "/admin/alerts", http.StatusFound)
		return
	}

	tmpl, err := parseTmpl("getLogin", markup)
	if err != nil {
		log.Printf("getLogin.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tmpl.Execute(w, nil); err != nil {
		log.Printf("getLogin.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postLogin(w http.ResponseWriter, r *http.Request) {
	username := r.PostFormValue("username")
	if username == "" {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Enter a username and password
			</div>
		`))
		return
	}

	password := r.PostFormValue("password")
	if password == "" {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Enter a username and password
			</div>
		`))
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postLogin.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	pwHash, userID, err := getPasswordHash(tx, username)
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusBadRequest)
			w.Write([]byte(`
				<div id="alert" class="alert" hx-swap-oob="true">
					Incorrect credentials
				</div>
			`))
			return
		}
		log.Printf("postLogin.getPasswordHash: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = bcrypt.CompareHashAndPassword([]byte(pwHash), []byte(password)); err != nil {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Incorrect credentials
			</div>
		`))
		return
	}

	tokenBytes := make([]byte, 32)
	_, err = rand.Read(tokenBytes)
	if err != nil {
		log.Printf("postLogin.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	csrfTokenBytes := make([]byte, 32)
	_, err = rand.Read(csrfTokenBytes)
	if err != nil {
		log.Printf("postLogin.Read2: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	token := base64.StdEncoding.EncodeToString(tokenBytes)
	csrfToken := base64.StdEncoding.EncodeToString(csrfTokenBytes)

	if err = createSession(tx, token, csrfToken, userID); err != nil {
		log.Printf("postLogin.createSession: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postLogin.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	http.SetCookie(
		w,
		&http.Cookie{
			Name:     "session",
			Value:    token,
			Path:     "/",
			Expires:  time.Now().UTC().Add(time.Hour * 876600),
			Secure:   BUILD == "release",
			HttpOnly: true,
			SameSite: http.SameSiteLaxMode,
		},
	)

	w.Header().Add("HX-Location", "/admin/alerts")
}

func adminIndex(w http.ResponseWriter, r *http.Request) {
	w.Header().Add("HX-Location", "/admin/alerts")
}

type AlertListing struct {
	ID        int
	Title     string
	AlertType string
	Severity  string
	CreatedAt *time.Time
	EndedAt   *time.Time
}

func listAlerts(tx *sql.Tx) ([]AlertListing, error) {
	const query = `
		select id, title, type, severity, created_at, ended_at from alert
		order by created_at desc
	`

	alerts := []AlertListing{}

	rows, err := tx.Query(query)
	if err != nil {
		return alerts, fmt.Errorf("listAlerts.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		alert := AlertListing{}
		err = rows.Scan(
			&alert.ID,
			&alert.Title,
			&alert.AlertType,
			&alert.Severity,
			&alert.CreatedAt,
			&alert.EndedAt,
		)
		if err != nil {
			return alerts, fmt.Errorf("listAlerts.Scan: %w", err)
		}

		alerts = append(alerts, alert)
	}

	return alerts, nil
}

func alerts(w http.ResponseWriter, r *http.Request) {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("alerts.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	alerts, err := listAlerts(tx)
	if err != nil {
		log.Printf("alerts.listAlerts: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("alerts.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Services{{end}}
		{{define "body"}}
			<div class="admin-nav-header">
				<div>
					<h2>Alerts</h2>
				</div>

				<div>
					<a href="/admin/alerts/notifications" hx-boost="true">
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
							<path fill-rule="evenodd" d="M10 2a6 6 0 0 0-6 6c0 1.887-.454 3.665-1.257 5.234a.75.75 0 0 0 .515 1.076 32.91 32.91 0 0 0 3.256.508 3.5 3.5 0 0 0 6.972 0 32.903 32.903 0 0 0 3.256-.508.75.75 0 0 0 .515-1.076A11.448 11.448 0 0 1 16 8a6 6 0 0 0-6-6ZM8.05 14.943a33.54 33.54 0 0 0 3.9 0 2 2 0 0 1-3.9 0Z" clip-rule="evenodd" />
						</svg>				  
					</a>
					<a href="/admin/alerts/create" hx-boost="true">
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
							<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
						</svg>
					</a>
				</div>
			</div>

			{{if eq (len .Alerts) 0}}
				<div class="entity-empty-state">
					<div class="icon">
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
							<path fill-rule="evenodd" d="M8.485 2.495c.673-1.167 2.357-1.167 3.03 0l6.28 10.875c.673 1.167-.17 2.625-1.516 2.625H3.72c-1.347 0-2.189-1.458-1.515-2.625L8.485 2.495zM10 5a.75.75 0 01.75.75v3.5a.75.75 0 01-1.5 0v-3.5A.75.75 0 0110 5zm0 9a1 1 0 100-2 1 1 0 000 2z" clip-rule="evenodd" />
				  		</svg>
					</div>
					<span>Create your first alert</span>
					<a class="action" href="/admin/alerts/create" hx-boost="true">Create alert</a>
				</div>
			{{else}}
				<div class="alerts-container">
					{{range $alert := .Alerts}}
						<a href="/admin/alerts/{{$alert.ID}}" hx-boost="true">
							<div>
								<div>
									{{if not $alert.EndedAt }}
										{{if eq $alert.AlertType "incident"}}
											<div class="live">LIVE</div>
										{{else}}
											<div class="active">ACTIVE</div>
										{{end}}
									{{end}}
									<span>{{$alert.CreatedAt}}</span>
								</div>
								<div class="swatch" style="background-color: var(--{{$alert.Severity}});">
								</div>
							</div>
							<span>{{$alert.Title}}</span>
						</a>
					{{end}}
				</div>
			{{end}}
		{{end}}
	`

	tmpl, err := parseTmpl("alerts", markup)
	if err != nil {
		log.Printf("alerts.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	type FormattedAlert struct {
		ID        int
		Title     string
		AlertType string
		Severity  string
		CreatedAt string
		EndedAt   string
	}

	formattedAlerts := make([]FormattedAlert, 0, len(alerts))
	for _, alert := range alerts {
		createdAt := alert.CreatedAt.Format("Jan 2 2006 • 15:04 MST")
		if alert.CreatedAt.Year() == time.Now().UTC().Year() {
			createdAt = alert.CreatedAt.Format("Jan 2 • 15:04 MST")
		}

		formattedAlert := FormattedAlert{
			ID:        alert.ID,
			Title:     alert.Title,
			AlertType: alert.AlertType,
			Severity:  alert.Severity,
			CreatedAt: createdAt,
		}
		if alert.EndedAt != nil {
			formattedAlert.EndedAt = alert.EndedAt.Format("02/01/2006 15:04 MST")
		}

		formattedAlerts = append(formattedAlerts, formattedAlert)
	}

	err = tmpl.Execute(
		w,
		struct {
			Alerts []FormattedAlert
			Ctx    pageCtx
		}{

			Alerts: formattedAlerts,
			Ctx:    getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("alerts.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

type Monitor struct {
	ID             int
	Name           string
	URL            string
	Method         string
	Frequency      int
	Timeout        int
	Attempts       int
	RequestHeaders map[string]string
	BodyFormat     sql.NullString
	Body           sql.NullString
}

func listMonitors(tx *sql.Tx) ([]Monitor, error) {
	const query = `
		select id, name, url, method, frequency, timeout, attempts, request_headers, 
			body_format, body
		from monitor
	`

	monitorListings := []Monitor{}

	rows, err := tx.Query(query)
	if err != nil {
		return monitorListings, fmt.Errorf("listMonitors.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var serializedRequestHeaders sql.NullString

		monitor := Monitor{}
		err = rows.Scan(
			&monitor.ID,
			&monitor.Name,
			&monitor.URL,
			&monitor.Method,
			&monitor.Frequency,
			&monitor.Timeout,
			&monitor.Attempts,
			&serializedRequestHeaders,
			&monitor.BodyFormat,
			&monitor.Body,
		)
		if err != nil {
			return monitorListings, fmt.Errorf("listMonitors.Scan: %w", err)
		}

		requestHeaders := map[string]string{}
		if serializedRequestHeaders.Valid {
			err = json.Unmarshal([]byte(serializedRequestHeaders.String), &requestHeaders)
			if err != nil {
				return monitorListings, fmt.Errorf("listMonitors.Unmarshal: %w", err)
			}
		}

		monitor.RequestHeaders = requestHeaders
		monitorListings = append(monitorListings, monitor)
	}

	return monitorListings, nil
}

func monitors(w http.ResponseWriter, r *http.Request) {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("monitors.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	monitors, err := listMonitors(tx)
	if err != nil {
		log.Printf("monitors.listMonitors: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	lastCheckedLogs, err := listAllMonitorLogLastChecked(tx)
	if err != nil {
		log.Printf("monitors.listAllMonitorLogLastChecked: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	monitorHappy := make(map[int]bool, len(lastCheckedLogs))
	for _, v := range lastCheckedLogs {
		monitorHappy[v.ID] = v.ResponseCode.Int32 != 0 && v.ResponseCode.Int32 < 400
	}

	const markup = `
		{{define "title"}}Monitors{{end}}
		{{define "body"}}
			<div class="admin-nav-header">
				<div>
					<h2>Monitors</h2>
				</div>

				<div>
					<a href="/admin/monitors/create" hx-boost="true">
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
							<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
						</svg>
					</a>
				</div>
			</div>

			{{if eq (len .Monitors) 0}}
				<div class="entity-empty-state">
					<div class="icon">
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
							<path d="M10 12.5a2.5 2.5 0 100-5 2.5 2.5 0 000 5z" />
							<path fill-rule="evenodd" d="M.664 10.59a1.651 1.651 0 010-1.186A10.004 10.004 0 0110 3c4.257 0 7.893 2.66 9.336 6.41.147.381.146.804 0 1.186A10.004 10.004 0 0110 17c-4.257 0-7.893-2.66-9.336-6.41zM14 10a4 4 0 11-8 0 4 4 0 018 0z" clip-rule="evenodd" />
						</svg>
					</div>
					<span>Create your first monitor</span>
					<a class="action" href="/admin/monitors/create" hx-boost="true">Create monitor</a>
				</div>
			{{else}}
				<div class="monitors-container">
					{{range $monitor := .Monitors}}
						<a hx-boost="true" href="/admin/monitors/{{$monitor.ID}}">
							<div>
								<span>{{$monitor.Name}}</span>
								<span>{{$monitor.URL}}</span>
							</div>
							{{if index $.MonitorHappy $monitor.ID}}
								<span class="badge">OK</span>
							{{else}}
								<span class="badge badge--error">Error</span>
							{{end}}
						</a>
					{{end}}
				</div>
			{{end}}
		{{end}}
	`

	tmpl, err := parseTmpl("monitors", markup)
	if err != nil {
		log.Printf("monitors.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Monitors     []Monitor
			MonitorHappy map[int]bool
			Ctx          pageCtx
		}{

			Monitors:     monitors,
			MonitorHappy: monitorHappy,
			Ctx:          getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("monitors.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getMonitorByID(tx *sql.Tx, id int) (Monitor, error) {
	const query = `
		select
			id,
			name,
			url,
			method,
			frequency,
			timeout,
			attempts,
			request_headers,
			body_format,
			body
		from
			monitor
		where
			id = ?
	`

	monitor := Monitor{}

	var serializedRequestHeaders sql.NullString

	err := tx.QueryRow(query, id).Scan(
		&monitor.ID,
		&monitor.Name,
		&monitor.URL,
		&monitor.Method,
		&monitor.Frequency,
		&monitor.Timeout,
		&monitor.Attempts,
		&serializedRequestHeaders,
		&monitor.BodyFormat,
		&monitor.Body,
	)
	if err != nil {
		return monitor, fmt.Errorf("getMonitorByID.QueryRow: %w", err)
	}

	requestHeaders := map[string]string{}

	if serializedRequestHeaders.Valid {
		err = json.Unmarshal([]byte(serializedRequestHeaders.String), &requestHeaders)
		if err != nil {
			return monitor, fmt.Errorf("getMonitorByID.Unmarshal: %w", err)
		}
	}

	monitor.RequestHeaders = requestHeaders

	return monitor, nil
}

type MonitorLog struct {
	ID           int
	StartedAt    time.Time
	EndedAt      time.Time
	ResponseCode sql.NullInt64
	ErrorMessage sql.NullString
	Attempts     int
	Result       string
	MonitorID    int
}

func listMonitorLogs(tx *sql.Tx, monitorID int, limit int, after int, before int, date time.Time) ([]MonitorLog, error) {
	query := `
		select
			id,
			started_at,
			ended_at,
			response_code,
			error_message,
			attempts,
			result,
			monitor_id
		from
			monitor_log
		where
			monitor_id = ?
	`

	if after != 0 {
		query += "and id < ?"
	}

	if before != 0 {
		query += " and id >= ?"
	}

	query += " and started_at >= ? and started_at < ?"

	query += "\norder by id desc"

	if limit > 0 {
		query += "\nlimit " + strconv.Itoa(limit)
	}

	monitorLogs := make([]MonitorLog, 0, limit)

	params := []any{monitorID}

	if after != 0 {
		params = append(params, after)
	}

	if before != 0 {
		params = append(params, before)
	}

	endOfDay := date.Add(time.Hour * 24)
	params = append(params, date, endOfDay)

	rows, err := tx.Query(query, params...)
	if err != nil {
		return monitorLogs, fmt.Errorf("listMonitorLogs.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		monitorLog := MonitorLog{}
		err = rows.Scan(
			&monitorLog.ID,
			&monitorLog.StartedAt,
			&monitorLog.EndedAt,
			&monitorLog.ResponseCode,
			&monitorLog.ErrorMessage,
			&monitorLog.Attempts,
			&monitorLog.Result,
			&monitorLog.MonitorID,
		)
		if err != nil {
			return monitorLogs, fmt.Errorf("listMonitorLogs.Scan: %w", err)
		}
		monitorLogs = append(monitorLogs, monitorLog)
	}

	return monitorLogs, nil
}

type MonitorLogView struct {
	ID           int
	StartedAt    string
	Latency      time.Duration
	ResponseCode sql.NullInt64
	ErrorMessage sql.NullString
	Attempts     int
	Result       string
	MonitorID    int
}

func getMonitor(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	dateParam := r.URL.Query().Get("date")
	if dateParam == "" {
		dateParam = time.Now().UTC().Format("2006-01-02")
	}

	date, err := time.Parse("2006-01-02", dateParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getMonitor.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	const logLimit = 100

	monitor, err := getMonitorByID(tx, id)
	if err != nil {
		log.Printf("getMonitor.getMonitorByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	monitorLogs, err := listMonitorLogs(tx, id, logLimit, 0, 0, date)
	if err != nil {
		log.Printf("getMonitor.listMonitorLogs: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	lastChecked, err := getMonitorLogLastChecked(tx, monitor.ID)
	if err != nil {
		log.Printf("getMonitor.getMonitorLogLastChecked: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("getMonitor.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if _, ok := r.URL.Query()["ready"]; ok {
		if len(monitorLogs) == 0 {
			w.WriteHeader(http.StatusNoContent)
			return
		}
	}

	const markup = `
		{{define "title"}}{{.Monitor.Name}} - Monitor{{end}}
		{{define "body"}}
			<div class="monitor-container">
				<div class="admin-nav-header monitor-header">
					<div>
						<a href="/admin/monitors" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
						<h2>{{.Monitor.Name}}</h2>
					</div>
					<div>
						<div>
							{{if len .Logs}}
								<div id="last-checked-status" class="badge{{if not .LastCheckedSuccess}} badge--error{{end}}">
									{{if .LastCheckedSuccess}}
										<span>OK</span>
									{{else}}
										<span>Error</span>
									{{end}}
								</div>
								<span id="next-refresh" class="next-refresh">
									{{.NextRefreshMsg}}
								</span>
							{{end}}
						</div>
						<div>
							<div id="get-monitor-menu" class="menu" hx-preserve>
								<button class="menu-button">
									<svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 12 12" fill="none">
										<path d="M5.99961 1.80005C6.2383 1.80005 6.46722 1.89487 6.63601 2.06365C6.80479 2.23244 6.89961 2.46135 6.89961 2.70005C6.89961 2.93874 6.80479 3.16766 6.63601 3.33645C6.46722 3.50523 6.2383 3.60005 5.99961 3.60005C5.76091 3.60005 5.532 3.50523 5.36321 3.33645C5.19443 3.16766 5.09961 2.93874 5.09961 2.70005C5.09961 2.46135 5.19443 2.23244 5.36321 2.06365C5.532 1.89487 5.76091 1.80005 5.99961 1.80005ZM5.99961 5.10005C6.2383 5.10005 6.46722 5.19487 6.63601 5.36365C6.80479 5.53244 6.89961 5.76135 6.89961 6.00005C6.89961 6.23874 6.80479 6.46766 6.63601 6.63645C6.46722 6.80523 6.2383 6.90005 5.99961 6.90005C5.76091 6.90005 5.532 6.80523 5.36321 6.63645C5.19443 6.46766 5.09961 6.23874 5.09961 6.00005C5.09961 5.76135 5.19443 5.53244 5.36321 5.36365C5.532 5.19487 5.76091 5.10005 5.99961 5.10005ZM6.89961 9.30005C6.89961 9.06135 6.80479 8.83244 6.63601 8.66365C6.46722 8.49487 6.2383 8.40005 5.99961 8.40005C5.76091 8.40005 5.532 8.49487 5.36321 8.66365C5.19443 8.83244 5.09961 9.06135 5.09961 9.30005C5.09961 9.53874 5.19443 9.76766 5.36321 9.93645C5.532 10.1052 5.76091 10.2 5.99961 10.2C6.2383 10.2 6.46722 10.1052 6.63601 9.93645C6.80479 9.76766 6.89961 9.53874 6.89961 9.30005Z" fill="#595959"/>
									</svg>
								</button>

								<dialog>
									<a href="/admin/monitors/{{.Monitor.ID}}/edit" hx-boost="true">Edit</a>
									<button onclick="document.getElementById('delete-dialog').showModal();">Delete</button>
								</dialog>
							</div>
							<dialog class="modal" id="delete-dialog">
								<span>Delete {{.Monitor.Name}}</span>
								<form hx-delete hx-swap="none">
									<div>
										<button onclick="document.getElementById('delete-dialog').close(); return false;">Cancel</button>
										<button>Delete</button>
									</div>
								</form>
							</dialog>
						</div>
					</div>
				</div>


				<div class="monitor-log-header">
					<h3>Logs</h3>
					
					<form hx-get="/admin/monitors/{{.Monitor.ID}}" hx-target="body" hx-swap="outerHTML">
						<input name="date" class="date-picker" type="date" value="{{.Date}}" required />
						<button class="date-picker-button">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M5.75 2a.75.75 0 01.75.75V4h7V2.75a.75.75 0 011.5 0V4h.25A2.75 2.75 0 0118 6.75v8.5A2.75 2.75 0 0115.25 18H4.75A2.75 2.75 0 012 15.25v-8.5A2.75 2.75 0 014.75 4H5V2.75A.75.75 0 015.75 2zm-1 5.5c-.69 0-1.25.56-1.25 1.25v6.5c0 .69.56 1.25 1.25 1.25h10.5c.69 0 1.25-.56 1.25-1.25v-6.5c0-.69-.56-1.25-1.25-1.25H4.75z" clip-rule="evenodd" />
							</svg>
						</button>
					</form>
				</div>

				<div id="monitor-time" class="monitor-time" hx-preserve>
					<span id="loader" class="loader"></span>
				</div>

				{{if len .Logs}}
					<div class="monitor-logs-container" 
						hx-get="/admin/monitors/{{.Monitor.ID}}/all?after={{.LastLogID}}&date={{.Date}}" 
						hx-trigger="load delay:500ms"
						hx-target=".monitor-logs-container"
						hx-swap="beforeend"
					>
						{{range $i, $log := .Logs}}
							<div 
								{{if index $.TimeIDs $log.ID}}id="{{index $.TimeIDs $log.ID}}"{{end}}
								{{if eq $i 0}}
									hx-get="/admin/monitors/{{$.Monitor.ID}}/poll?before={{$log.ID}}&date={{$.Date}}" 
									hx-trigger="load delay:{{$.RefreshDelay}}}s"
									hx-target="this"
									hx-swap="outerHTML"
								{{end}}
							>
								<span>{{$log.StartedAt}}</span>
								<span>{{$log.Latency}}</span>
								{{if eq $log.Result "error"}}
									<span class="badge{{if ge $log.ResponseCode.Int64 400}} badge--error{{end}}">
										{{$log.ResponseCode.Int64}}
									</span>
								{{end}}

								{{if eq $log.Result "success"}}
									<span class="badge">
										{{$log.ResponseCode.Int64}}
									</span>
								{{end}}

								{{if eq $log.Result "timeout"}}
									<span class="badge badge--error">
										TIMEOUT
									</span>
								{{end}}
							</div>
						{{end}}
					</div>
				{{else}}
					<div
						class="entity-empty-state"
						hx-get="/admin/monitors/{{.Monitor.ID}}?ready"
						hx-trigger="every 500ms"
						hx-target="body"
					>
						<div class="icon">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M15.312 11.424a5.5 5.5 0 01-9.201 2.466l-.312-.311h2.433a.75.75 0 000-1.5H3.989a.75.75 0 00-.75.75v4.242a.75.75 0 001.5 0v-2.43l.31.31a7 7 0 0011.712-3.138.75.75 0 00-1.449-.39zm1.23-3.723a.75.75 0 00.219-.53V2.929a.75.75 0 00-1.5 0V5.36l-.31-.31A7 7 0 003.239 8.188a.75.75 0 101.448.389A5.5 5.5 0 0113.89 6.11l.311.31h-2.432a.75.75 0 000 1.5h4.243a.75.75 0 00.53-.219z" clip-rule="evenodd" />
							</svg>
						</div>
						<span>Getting first logs...</span>
					</div>
				{{end}}
			</div>
			<script>
				(() => {
					const interval = setInterval(() => {
						const nextCheck = document.querySelector("#next-refresh");
						if (!nextCheck) {
							return
						}
						const num = nextCheck.innerText.slice(0, -1).split(" ").slice(-1);
						if (num > 0) {
							nextCheck.innerText = nextCheck.innerText.replace(num, (parseInt(num) - 1).toString());
						}
					}, 1000);

					function cleanup(e) {
						if (e.detail.elt.className === "root") {
							clearInterval(interval);
							document.removeEventListener("htmx:beforeCleanupElement", cleanup);
						}
					}					
					document.addEventListener("htmx:beforeCleanupElement", cleanup);


					const form = document.querySelector(".monitor-log-header form");

					const datePicker = document.querySelector(".date-picker");
					const datePickerButton = document.querySelector(".date-picker-button");
					datePickerButton.addEventListener("click", (e) => {
						e.preventDefault();
						datePicker.showPicker();
					});

					datePicker.addEventListener("change", () => {
						form.requestSubmit();
					});
				})();
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getMonitor", markup)
	if err != nil {
		log.Printf("getMonitor.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	refreshDelay := 5

	nextRefreshMsg := fmt.Sprintf(
		"Checking for updates in %ds",
		refreshDelay,
	)

	timeIDs := make(map[int]string, logLimit)
	for i, log := range monitorLogs {
		if i > 0 {
			lastLog := monitorLogs[i-1]
			if log.StartedAt.Hour() != lastLog.StartedAt.Hour() || log.StartedAt.Minute() != lastLog.StartedAt.Minute() {
				timeIDs[log.ID] = log.StartedAt.Format("15:04")
			}
		} else {
			timeIDs[log.ID] = log.StartedAt.Format("15:04")
		}
	}

	formattedMonitorLogs := make([]MonitorLogView, 0, len(monitorLogs))
	for _, log := range monitorLogs {
		formattedMonitorLogs = append(
			formattedMonitorLogs,
			MonitorLogView{
				ID:        log.ID,
				StartedAt: log.StartedAt.Format("2006/01/02 15:04:05 MST"),
				Latency: log.EndedAt.Sub(log.StartedAt).
					Round(time.Millisecond * 1),
				ResponseCode: log.ResponseCode,
				ErrorMessage: log.ErrorMessage,
				Attempts:     log.Attempts,
				Result:       log.Result,
				MonitorID:    log.MonitorID,
			},
		)
	}

	if dateParam != "" {
		w.Header().Set("HX-Push-Url", r.URL.Path+"?date="+dateParam)
	}

	lastLogID := 0
	if len(monitorLogs) > 0 {
		lastLogID = monitorLogs[len(monitorLogs)-1].ID
	}

	err = tmpl.Execute(
		w,
		struct {
			Monitor            Monitor
			Logs               []MonitorLogView
			NextRefreshMsg     string
			LastCheckedSuccess bool
			LastLogID          int
			TimeIDs            map[int]string
			RefreshDelay       int
			Ctx                pageCtx
			Date               string
		}{
			Monitor:            monitor,
			Logs:               formattedMonitorLogs,
			NextRefreshMsg:     nextRefreshMsg,
			LastCheckedSuccess: lastChecked.ResponseCode.Int32 != 0 && lastChecked.ResponseCode.Int32 < 400,
			LastLogID:          lastLogID,
			TimeIDs:            timeIDs,
			RefreshDelay:       refreshDelay,
			Date:               dateParam,
			Ctx:                getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getMonitor.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getMonitorAllLogs(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	afterParam := r.URL.Query().Get("after")
	if afterParam == "" {
		return
	}

	after, err := strconv.Atoi(afterParam)
	if err != nil {
		return
	}

	dateParam := r.URL.Query().Get("date")
	if dateParam == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	date, err := time.Parse("2006-01-02", dateParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getMonitorAllLogs.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	const logLimit = 2160

	monitorLogs, err := listMonitorLogs(tx, id, logLimit, after, 0, date)
	if err != nil {
		log.Printf("getMonitorAllLogs.listMonitorLogs: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("getMonitorAllLogs.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	lastLogID := 0
	if len(monitorLogs) > 0 {
		lastLogID = monitorLogs[len(monitorLogs)-1].ID
	}

	const markup = `
		{{range $log := .Logs}}
			<div {{if index $.TimeIDs $log.ID}}id="{{index $.TimeIDs $log.ID}}"{{end}}>
				<span>{{$log.StartedAt}}</span>
				<span>{{$log.Latency}}</span>
				{{if eq $log.Result "error"}}
					<span class="badge{{if ge $log.ResponseCode.Int64 400}} badge--error{{end}}">
						{{$log.ResponseCode.Int64}}
					</span>
				{{end}}

				{{if eq $log.Result "success"}}
					<span class="badge">
						{{$log.ResponseCode.Int64}}
					</span>
				{{end}}

				{{if eq $log.Result "timeout"}}
					<span class="badge badge--error">
						TIMEOUT
					</span>
				{{end}}
			</div>
			{{if eq $log.ID $.LastLogID }}
				<div
					style="display: none;" 
					hx-get="/admin/monitors/{{$.MonitorID}}/all?after={{$.LastLogID}}&date={{$.Date}}" 
					hx-trigger="load delay:500ms"
					hx-target=".monitor-logs-container"
					hx-swap="beforeend"
				>
				</div>
			{{end}}
		{{end}}
		{{if not (len .Logs)}}
			<div id="monitor-time" class="monitor-time" hx-swap-oob="true">
				<span id="loader" class="loader" style="display: none;"></span>

				<form>
					<input class="time-input" type="time" name="time" />
					<button>
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
							<path fill-rule="evenodd" d="M9 3.5a5.5 5.5 0 100 11 5.5 5.5 0 000-11zM2 9a7 7 0 1112.452 4.391l3.328 3.329a.75.75 0 11-1.06 1.06l-3.329-3.328A7 7 0 012 9z" clip-rule="evenodd" />
						</svg>
					</button>
				</form>
			</div>
			<script>
				(() => {
					const timeInputForm = document.querySelector(
						".monitor-time form"
					);

					const timeInput = document.querySelector(
						".time-input"
					);

					timeInput.addEventListener("change", () => {
						timeInput.setCustomValidity("");
						timeInput.reportValidity();
					});
	
					timeInputForm.addEventListener("submit", (e) => {
						e.preventDefault();
						
						const result = document.getElementById(timeInput.value); 
						
						if (result) {
							window.location.hash = timeInput.value;
							result.scrollIntoView();
						} else {
							timeInput.setCustomValidity("No results");
							timeInput.reportValidity();
						}
					});
				})();
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getMonitorAllLogs", markup)
	if err != nil {
		log.Printf("getMonitorAllLogs.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	formattedMonitorLogs := make([]MonitorLogView, 0, len(monitorLogs))
	for _, log := range monitorLogs {
		formattedMonitorLogs = append(
			formattedMonitorLogs,
			MonitorLogView{
				ID:        log.ID,
				StartedAt: log.StartedAt.Format("2006/01/02 15:04:05 MST"),
				Latency: log.EndedAt.Sub(log.StartedAt).
					Round(time.Millisecond * 1),
				ResponseCode: log.ResponseCode,
				ErrorMessage: log.ErrorMessage,
				Attempts:     log.Attempts,
				Result:       log.Result,
				MonitorID:    log.MonitorID,
			},
		)
	}

	timeIDs := make(map[int]string, logLimit)
	for i, log := range monitorLogs {
		if i > 0 {
			lastLog := monitorLogs[i-1]
			if log.StartedAt.Hour() != lastLog.StartedAt.Hour() ||
				log.StartedAt.Minute() != lastLog.StartedAt.Minute() {
				timeIDs[log.ID] = log.StartedAt.Format("15:04")
			}
		} else {
			timeIDs[log.ID] = log.StartedAt.Format("15:04")
		}
	}

	err = tmpl.Execute(
		w,
		struct {
			Logs      []MonitorLogView
			LastLogID int
			MonitorID int
			TimeIDs   map[int]string
			Date      string
		}{
			Logs:      formattedMonitorLogs,
			LastLogID: lastLogID,
			MonitorID: id,
			TimeIDs:   timeIDs,
			Date:      dateParam,
		},
	)
	if err != nil {
		log.Printf("getMonitorAllLogs.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getMonitorPoll(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	beforeParam := r.URL.Query().Get("before")
	if beforeParam == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	before, err := strconv.Atoi(beforeParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	dateParam := r.URL.Query().Get("date")
	if dateParam == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	date, err := time.Parse("2006-01-02", dateParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getMonitorPoll.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	monitorLogs, err := listMonitorLogs(tx, id, 0, 0, before, date)
	if err != nil {
		log.Printf("getMonitorPoll.listMonitorLogs: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	lastChecked, err := getMonitorLogLastChecked(tx, id)
	if err != nil {
		log.Printf("getMonitorPoll.getMonitorLogLastChecked: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("getMonitorPoll.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	refreshDelay := 5

	nextRefreshMsg := fmt.Sprintf(
		"Checking for updates in %ds",
		refreshDelay,
	)

	const markup = `
		<div id="last-checked-status" class="badge{{if not .LastCheckedSuccess}} badge--error{{end}}" hx-swap-oob="true">
			{{if .LastCheckedSuccess}}
				<span>OK</span>
			{{else}}
				<span>Error</span>
			{{end}}
		</div>

		<span id="next-refresh" class="next-refresh" hx-swap-oob="true">
			{{.NextRefreshMsg}}
		</span>

		{{range $i, $log := .Logs}}
			<div 
				{{if index $.TimeIDs $log.ID}}id="{{index $.TimeIDs $log.ID}}"{{end}}
				{{if eq $i 0}}
					hx-get="/admin/monitors/{{$.MonitorID}}/poll?before={{$log.ID}}&date={{$.Date}}" 
					hx-trigger="load delay:{{$.RefreshDelay}}s"
					hx-target="this"
					hx-swap="outerHTML"
				{{end}}
			>
				<span>{{$log.StartedAt}}</span>
				<span>{{$log.Latency}}</span>
				{{if eq $log.Result "error"}}
					<span class="badge{{if ge $log.ResponseCode.Int64 400}} badge--error{{end}}">
						{{$log.ResponseCode.Int64}}
					</span>
				{{end}}

				{{if eq $log.Result "success"}}
					<span class="badge">
						{{$log.ResponseCode.Int64}}
					</span>
				{{end}}

				{{if eq $log.Result "timeout"}}
					<span class="badge badge--error">
						TIMEOUT
					</span>
				{{end}}
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getMonitorPoll", markup)
	if err != nil {
		log.Printf("getMonitorPoll.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	formattedMonitorLogs := make([]MonitorLogView, 0, len(monitorLogs))
	for _, log := range monitorLogs {
		formattedMonitorLogs = append(
			formattedMonitorLogs,
			MonitorLogView{
				ID:        log.ID,
				StartedAt: log.StartedAt.Format("2006/01/02 15:04:05 MST"),
				Latency: log.EndedAt.Sub(log.StartedAt).
					Round(time.Millisecond * 1),
				ResponseCode: log.ResponseCode,
				ErrorMessage: log.ErrorMessage,
				Attempts:     log.Attempts,
				Result:       log.Result,
				MonitorID:    log.MonitorID,
			},
		)
	}

	timeIDs := make(map[int]string, len(formattedMonitorLogs))
	for i, log := range monitorLogs {
		if i > 0 {
			lastLog := monitorLogs[i-1]
			if log.StartedAt.Hour() != lastLog.StartedAt.Hour() ||
				log.StartedAt.Minute() != lastLog.StartedAt.Minute() {
				timeIDs[log.ID] = log.StartedAt.Format("15:04")
			}
		} else {
			timeIDs[log.ID] = log.StartedAt.Format("15:04")
		}
	}

	err = tmpl.Execute(
		w,
		struct {
			Logs               []MonitorLogView
			LastLogID          int
			MonitorID          int
			TimeIDs            map[int]string
			RefreshDelay       int
			NextRefreshMsg     string
			LastCheckedSuccess bool
			Date               string
		}{
			Logs:               formattedMonitorLogs,
			MonitorID:          id,
			TimeIDs:            timeIDs,
			RefreshDelay:       5,
			NextRefreshMsg:     nextRefreshMsg,
			LastCheckedSuccess: lastChecked.ResponseCode.Int32 != 0 && lastChecked.ResponseCode.Int32 < 400,
			Date:               dateParam,
		},
	)
	if err != nil {
		log.Printf("getMonitorPoll.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getEditMonitor(w http.ResponseWriter, r *http.Request) {
	refreshID := r.URL.Query().Get("refresh")
	id, _ := strconv.Atoi(chi.URLParam(r, "id"))

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getEditMonitor.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	monitor, err := getMonitorByID(tx, id)
	if err != nil {
		log.Printf("getEditMonitor.getMonitorByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	channels, err := listNotificationChannels(tx, listNotificationsOptions{})
	if err != nil {
		log.Printf("getEditMonitor.listNotificationChannels: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	monitorNotificationChannels, err := listNotificationChannelsByMonitorID(tx, monitor.ID)
	if err != nil {
		log.Printf("getEditMonitor.listNotificationChannelsByMonitorID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	monitorNotificationsMap := map[int]bool{}
	for _, v := range monitorNotificationChannels {
		monitorNotificationsMap[v.ID] = true
	}

	mailGroups, err := listMailGroups(tx)
	if err != nil {
		log.Printf("getEditMonitor.mailGroups: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	selectedMailGroups, err := listMailGroupIDsByMonitorID(tx, monitor.ID)
	if err != nil {
		log.Printf("getEditMonitor.listMailGroupIDsByMonitorID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	selectedMailGroupsMap := map[int]bool{}
	for _, v := range selectedMailGroups {
		selectedMailGroupsMap[v] = true
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getEditMonitor.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Edit monitor{{end}}
		{{define "body"}}
			<div class="create-monitor-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/monitors/{{.Monitor.ID}}" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
				
						<h2>Edit monitor</h2>
					</div>
				</div>

				<form hx-post hx-swap="none" autocomplete="off">
					<label>
						Name
						<input name="name" placeholder="My website" value="{{.Monitor.Name}}" required />
					</label>

					<label>
						URL
						<span id="alert-error"></span>
						<input 
							name="url"
							type="url"
							placeholder="https://example.com"
							value="{{.Monitor.URL}}"
							required
						>
					</label>
					
					<div>
						<div>
							<label>
								HTTP method
							</label>
							<div class="checkbox-group">
								<label>
									<input 
										name="method" 
										{{if eq .Monitor.Method "GET"}}checked{{end}}
										type="radio"
										value="GET"
										onclick="handleMethodChange(this);"
										required
									/>
									GET
								</label>
								<label>
									<input
										name="method"
										{{if eq .Monitor.Method "POST"}}checked{{end}}
										type="radio"
										value="POST"
										onclick="handleMethodChange(this);"
										required
									/>
									POST
								</label>
								<label>
									<input
										name="method"
										{{if eq .Monitor.Method "PATCH"}}checked{{end}}
										type="radio"
										value="PATCH"
										onclick="handleMethodChange(this);"
										required
									/>
									PATCH
								</label>
								<label>
									<input 
										name="method"
										{{if eq .Monitor.Method "PUT"}}checked{{end}}
										type="radio"
										value="PUT"
										onclick="handleMethodChange(this);"
										required
									/>
									PUT
								</label>
								<label>
									<input 
										name="method"
										{{if eq .Monitor.Method "DELETE"}}checked{{end}}
										type="radio"
										value="DELETE"
										onclick="handleMethodChange(this);"
										required
									/>
									DELETE
								</label>
							</div>
						</div>	

						<div>
							<label>
								Frequency
							</label>
							<div class="checkbox-group">
								<label>
									<input name="frequency" {{if eq .Monitor.Frequency 10}}checked{{end}} type="radio" value="10" required/>
									10 seconds
								</label>
								<label>
									<input name="frequency" {{if eq .Monitor.Frequency 30}}checked{{end}} type="radio" value="30" required/>
									30 seconds
								</label>
								<label>
									<input name="frequency" {{if eq .Monitor.Frequency 60}}checked{{end}} type="radio" value="60" required/>
									1 minute
								</label>
							</div>
						</div>	

						<div>
							<label>
								Timeout
							</label>
							<div class="checkbox-group">
								<label>
									<input name="timeout" {{if eq .Monitor.Timeout 5}}checked{{end}} type="radio" value="5" required/>
									5 seconds
								</label>
								<label>
									<input name="timeout" {{if eq .Monitor.Timeout 10}}checked{{end}} type="radio" value="10" required/>
									10 seconds
								</label>
								<label>
									<input name="timeout" {{if eq .Monitor.Timeout 15}}checked{{end}} type="radio" value="15" required/>
									15 seconds
								</label>
							</div>
						</div>

						<div>
							<label>
								Attempt(s)
							</label>
							<div class="checkbox-group">
								<label>
									<input name="attempts" {{if eq .Monitor.Attempts 1}}checked{{end}} type="radio" value="1" required/>
									1
								</label>
								<label>
									<input name="attempts" {{if eq .Monitor.Attempts 2}}checked{{end}} type="radio" value="2" required/>
									2
								</label>
								<label>
									<input name="attempts" {{if eq .Monitor.Attempts 3}}checked{{end}} type="radio" value="3" required/>
									3
								</label>
							</div>
						</div>
					</div>

					<div class="request-headers-container">
						<fieldset class="param-box">
							<legend>Request headers</legend>
							<div 
								class="entity-empty-state entity-empty-state--secondary"
								{{if .Monitor.RequestHeaders}}style="display: none;"{{end}}
							>
								<div class="icon">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
										<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
									</svg>
								</div>
								<span>No headers set</span>
								<button
									class="action"
									type="button"
									onclick="addParamOnClick(this);"
								>
									Add header
								</button>
							</div>
							<fieldset 
								class="param-box__inputs"
								{{if not .Monitor.RequestHeaders}}disabled{{end}}
							>
								<legend class="hide">Request headers list</legend>
								<div class="param-box__list">
									{{if len .Monitor.RequestHeaders}}
										{{range $k, $v := .Monitor.RequestHeaders}}
											<div class="param-box__item">
												<input name="header-key" required placeholder="Key" value="{{$k}}" />
												<input name="header-value" required placeholder="Value" value="{{$v}}" />
												<button type="button" onclick="removeParamOnClick(this);">
													<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
														<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
													</svg>
												</button>
											</div>
										{{end}}
									{{else}}
										<div class="param-box__item">
											<input name="header-key" required placeholder="Key" />
											<input name="header-value" required placeholder="Value" />
											<button type="button" onclick="removeParamOnClick(this);">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
													<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
												</svg>
											</button>
										</div>
									{{end}}
								</div>
								<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
									<div>
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
											<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
										</svg>
									</div>
									<span>Add header</span>
								</button>
							</fieldset>
						</fieldset>
					</div>

					<div 
						id="request-body-container"
						style="{{if eq .Monitor.Method "GET"}}display: none;{{end}}
								{{if eq .Monitor.Method "DELETE"}}display: none;{{end}}
						"
					>
						<div class="request-body">
							<label>
								Request body
							</label>

							<div>
								<div>
									<input 
										type="radio"
										name="format"
										value="text"
										onchange="handleFormatChange(this);"
										{{if not (or (eq .Monitor.Method "GET") (eq .Monitor.Method "DELETE"))}}required{{end}}
										{{if eq .Monitor.BodyFormat.String "text"}}checked{{end}}
										{{if eq .Monitor.BodyFormat.String ""}}checked{{end}}
									/>
									<span>Text</span>
								</div>
								<div>
									<input 
										type="radio"
										name="format"
										value="form"
										onchange="handleFormatChange(this);"
										{{if not (or (eq .Monitor.Method "GET") (eq .Monitor.Method "DELETE"))}}required{{end}}
										{{if eq .Monitor.BodyFormat.String "form"}}checked{{end}}
									/>
									<span>Form</span>
								</div>
							</div>
						</div>

						<div 
							id="editor-container"
							style="width: 100%; height: 600px; margin-top: 1.0rem;{{if eq .Monitor.BodyFormat.String "form"}}display: none;{{end}}">
						</div>
						<input
							name="body"
							value="{{.TextBody}}"
							type="hidden"
						/>
						<fieldset id="body-param-box" class="param-box">
							<legend class="hide">Form values</legend>
							<div 
								class="entity-empty-state entity-empty-state--secondary"
								{{if or (len .FormData) (ne .Monitor.BodyFormat.String "form")}}style="display: none;"{{end}}
							>
								<div class="icon">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
										<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
									</svg>
								</div>
								<span>No parameters set</span>
								<button
									class="action"
									type="button"
									onclick="addParamOnClick(this);"
								>
									Add parameter
								</button>
							</div>
							<fieldset class="param-box__inputs" {{if not (len .FormData)}}disabled{{end}}>
								<div class="param-box__list">
									{{if and (eq .Monitor.BodyFormat.String "form") (len .FormData)}}
										{{range $key, $values := .FormData}}
											<div class="param-box__item">
												<input 
													name="form-key"
													required
													placeholder="Key"
													value="{{$key}}"
												/>
												<input
													name="form-value"
													required
													placeholder="Value"
													value="{{index $values 0}}"
												/>
												<button type="button" onclick="removeParamOnClick(this);">
													<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
														<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
													</svg>
												</button>
											</div>
										{{end}}
									{{else}}
										<div class="param-box__item">
											<input name="form-key" required placeholder="Key" />
											<input name="form-value" required placeholder="Value" />
											<button type="button" onclick="removeParamOnClick(this);">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
													<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
												</svg>
											</button>
										</div>
									{{end}}
								</div>
								<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
									<div>
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
											<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
										</svg>
									</div>
									<span>Add parameter</span>
								</button>
							</fieldset>
						</fieldset>
					</div>

					<div 
						id="notification-channels"
						class="notification-channels"
						{{if eq .RefreshID "notification-channels"}}hx-swap-oob="true"{{end}}
					>
						<label>
							<span>Notification channels</span>
						</label>

						{{if not (len .Notifications)}}
							<div
								class="entity-empty-state entity-empty-state--secondary" 
								style="margin-top: 1.0rem;"
							>
								<div class="icon">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
										<path fill-rule="evenodd" d="M10 2a6 6 0 0 0-6 6c0 1.887-.454 3.665-1.257 5.234a.75.75 0 0 0 .515 1.076 32.91 32.91 0 0 0 3.256.508 3.5 3.5 0 0 0 6.972 0 32.903 32.903 0 0 0 3.256-.508.75.75 0 0 0 .515-1.076A11.448 11.448 0 0 1 16 8a6 6 0 0 0-6-6ZM8.05 14.943a33.54 33.54 0 0 0 3.9 0 2 2 0 0 1-3.9 0Z" clip-rule="evenodd" />
									</svg> 
								</div>
								<span>No notification channels found</span>
								<div class="actions">
									<a class="action" href="/admin/notifications/create" target="_blank">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
											<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
										</svg>
										Add channel
									</a>
									<button type="button" class="empty-state-refresh" hx-get="?refresh=notification-channels">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
										</svg>
										Refresh
									</button>
								</div>
							</div>
						{{end}}

						<div class="notification-channels-group">
							{{range $notification := .Notifications}}
								<label>
									<input 
										type="checkbox"
										name="notification-channels"
										value="{{$notification.ID}}"
										{{if index $.MonitorNotifications $notification.ID}}checked{{end}}
									/>
									<span>
										{{if eq $notification.Type "smtp"}}
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
												<path d="M3 4a2 2 0 00-2 2v1.161l8.441 4.221a1.25 1.25 0 001.118 0L19 7.162V6a2 2 0 00-2-2H3z" />
												<path d="M19 8.839l-7.77 3.885a2.75 2.75 0 01-2.46 0L1 8.839V14a2 2 0 002 2h14a2 2 0 002-2V8.839z" />
											</svg>
										{{else if eq $notification.Type "slack"}}
											<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
												<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
												<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
												<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
												<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
												<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
												<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
												<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
												<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
											</svg>
										{{end}}
										{{$notification.Name}}
									</span>
								</label>
							{{end}}
						</div>
					</div>

					<fieldset
						id="notification-mail-groups"
						class="notification-mail-groups"
						{{if eq .RefreshID "notification-mail-groups"}}hx-swap-oob="true"{{end}}
					>
						<legend>
							Mail groups
						</legend>

						{{if not (len .MailGroups)}}
							<div
								class="entity-empty-state entity-empty-state--secondary" 
								style="margin-top: 1.0rem;"
							>
								<div class="icon">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
										<path d="M3 4a2 2 0 0 0-2 2v1.161l8.441 4.221a1.25 1.25 0 0 0 1.118 0L19 7.162V6a2 2 0 0 0-2-2H3Z" />
										<path d="m19 8.839-7.77 3.885a2.75 2.75 0 0 1-2.46 0L1 8.839V14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2V8.839Z" />
									</svg>  
								</div>
								<span>
									No mail groups found
								</span>
								<div class="actions">
									<a class="action" href="/admin/notifications/mail-groups/create" target="_blank">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
											<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
										</svg>
										Add mail group
									</a>
									<button type="button" class="empty-state-refresh" hx-get="?refresh=notification-mail-groups">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
										</svg>
										Refresh
									</button>
								</div>
							</div>
						{{end}}

						<div class="notification-mail-groups-group">
							{{range $mailGroup := .MailGroups}}
								<label>
									<input 
										type="checkbox"
										name="mail-groups"
										value="{{$mailGroup.ID}}"
										{{if index $.SelectedMailGroups $mailGroup.ID}}checked{{end}}
									/>
									<span>
										<span>
											{{$mailGroup.Name}}
										</span>
										<span>
											{{$mailGroup.Description}}
										</span>
									</span>
								</label>
							{{end}}
						</div>
					</fieldset>
					
					<div>
						<button type="submit">Edit</button>
					</div>

					<link
						rel="stylesheet"
						data-name="vs/editor/editor.main"
						href="/static/monaco-editor/min/vs/editor/editor.main.css"
					/>
			
					<script>
						var require = { paths: { vs: '/static/monaco-editor/min/vs' } };
					</script>
					
					<script>
						function addParamOnClick(e) {
							const root = e.closest(".param-box");

							const paramBoxInputs = root.querySelector(".param-box__inputs");

							if (paramBoxInputs.disabled) {
								paramBoxInputs.disabled = false;
								root.querySelector(".entity-empty-state").style.display = "none";
								return;
							}

							const items = root.querySelectorAll(".param-box__item")

							const clone = items[0].cloneNode(true);

							const paramBoxList = root.querySelector(".param-box__list")
									
							const insertedClone = paramBoxList.appendChild(
								clone,
							);

							insertedClone.querySelectorAll("input").forEach(v => {
								v.value = "";
							});
						}
						
						function removeParamOnClick(e) {
							const root = e.closest(".param-box");

							const paramBoxInputs = root.querySelector(".param-box__inputs");
							
							const items = paramBoxInputs.querySelectorAll(".param-box__item");
							if (items.length === 1) {								
								const emptyState = root.querySelector(".entity-empty-state");
								emptyState.style.display = "flex";
								root.querySelector(".param-box__inputs").disabled = true;
								[...root.querySelectorAll("input")].forEach(v => v.value = "");
							} else {
								e.parentElement.remove();
							}
						}

						function handleFormatChange(e) {
							const form = e.closest("form");
							
							const format = e.value;

							const editorContainer = document.getElementById("editor-container");
							const paramBox = document.querySelector("#body-param-box");

							if (format === "form") {
								e.form.elements["body"].disabled = true;
								editorContainer.style.display = "none";
								paramBox.style.display = "block";
								paramBox.disabled = false;
								if (format === "form") {
									if (
										form.elements["form-key"].value ||
										form.elements["form-value"].value ||
										form.elements["form-key"].length
									) {
										paramBox.querySelector(".param-box__inputs").disabled = false;
									} else {
										paramBox.querySelector(".entity-empty-state").style.display = "flex";
									}
								}
							} else if (format === "text") {
								e.form.elements["body"].disabled = false;
								editorContainer.style.display = "block";
								paramBox.style.display = "none";
								paramBox.disabled = true;
								paramBox.querySelector(".param-box__inputs").disabled = true;
							}
						}

						function handleMethodChange(e) {
							const form = e.closest("form");

							const format = form.elements["format"];

							const bodyContainer = document.querySelector("#request-body-container");

							const paramBox = document.querySelector("#body-param-box");

							if (["GET", "DELETE"].includes(e.value)) {
								bodyContainer.style.display = "none";
								form.elements["format"].forEach(v => {
									v.disabled = true;
								});
								paramBox.querySelector(".param-box__inputs").disabled = true;
								form.elements["body"].disabled = true;	
							}

							if (["POST", "PATCH", "PUT"].includes(e.value)) {
								bodyContainer.style.display = "block";
								form.elements["format"].forEach(v => {
									v.disabled = false;
								});
								if (format.value === "form") {
									if (
										form.elements["form-key"].value ||
										form.elements["form-value"].value ||
										form.elements["form-key"].length
									) {
									  paramBox.querySelector(".param-box__inputs").disabled = false;
									} else {
									  paramBox.querySelector(".entity-empty-state").style.display = "flex";
									}
								  }
								form.elements["body"].disabled = format.value !== "text";
							}
						}

						(async () => {
							function addScript(url) {
								return new Promise((resolve, reject) => {
									const script = document.createElement('script');
									script.onload = () => {
										resolve();
									};
									script.onerror = reject;
									script.src = url;
									document.body.appendChild(script);
								});
							}

							const form = document.querySelector("form");

							if (window.monaco) {
								window.monaco.editor.getModels().forEach(model => model.dispose());
								initEditor();
							}

							function initEditor() {
								const editor = monaco.editor.create(document.getElementById("editor-container"), {
									language: 'json',
									fontSize: 16,
									theme: "vs-dark",
									minimap: {enabled: false},
									overviewRulerLanes: 0,
									padding: {top: 24},
									automaticLayout: true,
									value: "{{.TextBody}}",
								});	
																	
								editor.getModel().onDidChangeContent((event) => {
									form.elements["body"].value = editor.getModel().getValue();
								});
							}

							if (!window.monaco) {
								await addScript("/static/monaco-editor/min/vs/loader.js");
								await addScript("/static/monaco-editor/min/vs/editor/editor.main.nls.js");
								await addScript("/static/monaco-editor/min/vs/editor/editor.main.js");
								initEditor();
							}
						})();
					</script>
				</form>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getEditMonitor", markup)
	if err != nil {
		log.Printf("getEditMonitor.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	textBody := ""
	if monitor.BodyFormat.String == "text" {
		textBody = monitor.Body.String
	}

	formData := url.Values{}
	if monitor.BodyFormat.String == "form" {
		data, err := url.ParseQuery(monitor.Body.String)
		if err != nil {
			log.Printf("getEditMonitor.ParseQuery: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
		formData = data
	}

	err = tmpl.Execute(
		w,
		struct {
			Monitor              Monitor
			TextBody             string
			FormData             url.Values
			Notifications        []NotificationChannel
			MonitorNotifications map[int]bool
			MailGroups           []MailGroup
			SelectedMailGroups   map[int]bool
			RefreshID            string
			Ctx                  pageCtx
		}{
			Monitor:              monitor,
			TextBody:             textBody,
			FormData:             formData,
			Notifications:        channels,
			MonitorNotifications: monitorNotificationsMap,
			MailGroups:           mailGroups,
			SelectedMailGroups:   selectedMailGroupsMap,
			RefreshID:            refreshID,
			Ctx:                  getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getEditMonitor.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func editMonitor(
	tx *sql.Tx,
	id int,
	name string,
	url string,
	method string,
	frequency int,
	timeout int,
	attempts int,
	requestHeaders sql.NullString,
	bodyFormat sql.NullString,
	body sql.NullString,
) (int, error) {
	const query = `
		update monitor set name = ?, url = ?, method = ?, frequency = ?, timeout = ?, 
			attempts = ?, request_headers = ?, body_format = ?, body = ?
		where id = ?
	`

	var monitorID int
	_, err := tx.Exec(
		query,
		name,
		url,
		method,
		frequency,
		timeout,
		attempts,
		requestHeaders,
		bodyFormat,
		body,
		id,
	)
	if err != nil {
		return monitorID, fmt.Errorf("editMonitor.QueryRow: %w", err)
	}

	return id, nil
}

func postEditMonitor(w http.ResponseWriter, r *http.Request) {
	name := r.PostFormValue("name")
	if name == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	reqURL := r.PostFormValue("url")
	validURL := true
	parsedReqURL, err := url.Parse(reqURL)
	if err != nil {
		validURL = false
	} else if parsedReqURL.Scheme == "" || parsedReqURL.Host == "" {
		validURL = false
	} else if parsedReqURL.Scheme != "http" && parsedReqURL.Scheme != "https" {
		validURL = false
	}

	if !validURL {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<span id="alert-error" hx-swap-oob="true">
				Invalid URL
			</span>
		`))
		return
	}

	method := r.PostFormValue("method")
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if method != http.MethodGet &&
		method != http.MethodPost &&
		method != http.MethodPatch &&
		method != http.MethodPut &&
		method != http.MethodDelete {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	frequency, err := strconv.Atoi(r.PostFormValue("frequency"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if frequency != 10 && frequency != 30 && frequency != 60 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	timeout, err := strconv.Atoi(r.PostFormValue("timeout"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if timeout != 5 && timeout != 10 && timeout != 15 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	attempts, err := strconv.Atoi(r.PostFormValue("attempts"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if attempts != 1 && attempts != 2 && attempts != 3 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	requestHeaders := sql.NullString{}
	requestHeadersMap := map[string]string{}
	if r.PostFormValue("header-key") != "" && r.PostFormValue("header-value") != "" {
		for i := range r.Form["header-key"] {
			requestHeadersMap[r.Form["header-key"][i]] = r.Form["header-value"][i]
		}
	}
	requestHeadersSerialized, err := json.Marshal(requestHeadersMap)
	if err != nil {
		log.Printf("postEditMonitor.Marshal: %s", err)
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if len(requestHeadersMap) > 0 {
		requestHeaders = sql.NullString{
			Valid:  true,
			String: string(requestHeadersSerialized),
		}
	}

	bodyFormat := sql.NullString{}
	if r.PostFormValue("format") != "" {
		bodyFormat = sql.NullString{
			Valid:  true,
			String: r.PostFormValue("format"),
		}
	}

	body := sql.NullString{}
	if r.PostFormValue("body") != "" {
		body = sql.NullString{
			Valid:  true,
			String: r.PostFormValue("body"),
		}
	}

	if r.PostFormValue("form-key") != "" && r.PostFormValue("form-value") != "" {
		urlValues := url.Values{}
		for i := 0; i < len(r.Form["form-key"]); i++ {
			urlValues.Add(r.Form["form-key"][i], r.Form["form-value"][i])
		}
		body = sql.NullString{
			Valid:  true,
			String: urlValues.Encode(),
		}
	}

	notificationChannelsParam := r.PostForm["notification-channels"]
	notificationChannels := make([]int, 0, len(notificationChannelsParam))
	for _, channelID := range notificationChannelsParam {
		id, err := strconv.Atoi(channelID)
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		notificationChannels = append(notificationChannels, id)
	}

	mailGroupsParam := r.PostForm["mail-groups"]
	mailGroups := make([]int, 0, len(mailGroupsParam))
	for _, channelID := range mailGroupsParam {
		id, err := strconv.Atoi(channelID)
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		mailGroups = append(mailGroups, id)
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postEditMonitor.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	idParam := chi.URLParam(r, "id")
	monitorID, err := strconv.Atoi(idParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	_, err = getMonitorByID(tx, monitorID)
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		log.Printf("postEditMonitor.getMonitorByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	_, err = editMonitor(
		tx,
		monitorID,
		name,
		reqURL,
		method,
		frequency,
		timeout,
		attempts,
		requestHeaders,
		bodyFormat,
		body,
	)
	if err != nil {
		log.Printf("postEditMonitor.createMonitor: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMonitorNotificationChannels(tx, monitorID, notificationChannels)
	if err != nil {
		log.Printf("postEditMonitor.updateMonitorNotificationChannels: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMonitorMailGroups(tx, monitorID, mailGroups)
	if err != nil {
		log.Printf("postEditMonitor.updateMonitorMailGroups: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postEditMonitor.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/monitors/"+idParam)
}

func deleteMonitorByID(tx *sql.Tx, id int) error {
	const query = `
		delete from monitor where id = ?
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("deleteMonitorByID.Exec: %w", err)
	}

	return nil
}

func deleteMonitor(w http.ResponseWriter, r *http.Request) {
	id, _ := strconv.Atoi(chi.URLParam(r, "id"))

	tx, err := rwDB.Begin()
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		log.Printf("deleteMonitor.Begin: %s", err)
		return
	}
	defer tx.Rollback()

	err = deleteMonitorByID(tx, id)
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		log.Printf("deleteMonitor.deleteMonitorByID: %s", err)
		return
	}

	err = tx.Commit()
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		log.Printf("deleteMonitor.Commit: %s", err)
		return
	}

	w.Header().Add("HX-Location", "/admin/monitors")
}

func getCreateMonitor(w http.ResponseWriter, r *http.Request) {
	refreshID := r.URL.Query().Get("refresh")

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getCreateMonitor.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	notifications, err := listNotificationChannels(tx, listNotificationsOptions{})
	if err != nil {
		log.Printf("getCreateMonitor.listNotificationChannels: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	mailGroups, err := listMailGroups(tx)
	if err != nil {
		log.Printf("getEditMonitor.mailGroups: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getCreateMonitor.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
			{{define "title"}}Create monitor{{end}}
			{{define "body"}}
				<div class="create-monitor-container">
					<div class="admin-nav-header">
						<div>
							<a href="/admin/monitors" hx-boost="true">
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
									<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
								</svg>								
							 </a>
					  
							<h2>Create monitor</h2>
						</div>
					</div>
	
					<form hx-post hx-swap="none" autocomplete="off">
						<label>
							Name
							<input name="name" placeholder="My website" required />
						</label>
	
						<label>
							URL
							<span id="alert-error"></span>
							<input
								name="url"
								type="url"
								placeholder="https://example.com"
								required
							>
						</label>
						
						<div>
							<div>
								<label>
									HTTP method
								</label>
								<div class="checkbox-group">
									<label>
										<input
											name="method"
											type="radio"
											value="GET"
											onclick="handleMethodChange(this);"
											checked
											required
										/>
										GET
									</label>
									<label>
										<input
											name="method"
											type="radio"
											value="POST"
											onclick="handleMethodChange(this);"
											required
										/>
										POST
									</label>
									<label>
										<input
											name="method"
											type="radio"
											value="PATCH"
											onclick="handleMethodChange(this);"
											required
										/>
										PATCH
									</label>
									<label>
										<input
											name="method"
											type="radio"
											value="PUT"
											onclick="handleMethodChange(this);"
											required
										/>
										PUT
									</label>
									<label>
										<input 
											name="method"
											type="radio"
											value="DELETE"
											onclick="handleMethodChange(this);"
											required
										/>
										DELETE
									</label>
								</div>
							</div>	

							<div>
								<label>
									Frequency
								</label>
								<div class="checkbox-group">
									<label>
										<input name="frequency" type="radio" value="10" checked required/>
										10 seconds
									</label>
									<label>
										<input name="frequency" type="radio" value="30" required/>
										30 seconds
									</label>
									<label>
										<input name="frequency" type="radio" value="60" required/>
										1 minute
									</label>
								</div>
							</div>	

							<div>
								<label>
									Timeout
								</label>
								<div class="checkbox-group">
									<label>
										<input name="timeout" type="radio" value="5" checked required/>
										5 seconds
									</label>
									<label>
										<input name="timeout" type="radio" value="10" required/>
										10 seconds
									</label>
									<label>
										<input name="timeout" type="radio" value="15" required/>
										15 seconds
									</label>
								</div>
							</div>

							<div>
								<label>
									Attempt(s)
								</label>
								<div class="checkbox-group">
									<label>
										<input name="attempts" type="radio" value="1" checked required/>
										1
									</label>
									<label>
										<input name="attempts" type="radio" value="2" required/>
										2
									</label>
									<label>
										<input name="attempts" type="radio" value="3" required/>
										3
									</label>
								</div>
							</div>
						</div>

						<div class="request-headers-container">
							<fieldset class="param-box">
								<legend>Request headers</legend>
								<div class="entity-empty-state entity-empty-state--secondary">
									<div class="icon">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
										</svg>
									</div>
									<span>No headers set</span>
									<button
										class="action"
										type="button"
										onclick="addParamOnClick(this);"
									>
										Add header
									</button>
								</div>
								<fieldset class="param-box__inputs" disabled>
									<legend class="hide">Request headers list</legend>
									<div class="param-box__list">
										<div class="param-box__item">
											<input name="header-key" required placeholder="Key" />
											<input name="header-value" required placeholder="Value" />
											<button type="button" onclick="removeParamOnClick(this);">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
													<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
												</svg>
											</button>
										</div>
									</div>
									<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
										<div>
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
												<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
											</svg>
										</div>
										<span>Add header</span>
									</button>
								</fieldset>
							</fieldset>
						</div>


						<div id="request-body-container" style="display: none;">
							<div class="request-body">
								<label>
									Request body
								</label>

								<div>
									<div>
										<input 
											type="radio"
											name="format"
											value="text"
											required
											checked
											onchange="handleFormatChange(this);"
										/>
										<span>Text</span>
									</div>
									<div>
										<input
											type="radio" 
											name="format"
											value="form"
											onchange="handleFormatChange(this);" 
											required/>
										<span>Form</span>
									</div>
								</div>
							</div>

							<div id="editor-container" style="width: 100%; height: 600px; margin-top: 1.0rem;"></div>
							<input name="body" required type="hidden"/>
							<fieldset id="body-param-box" class="param-box">
								<legend class="hide">Form values</legend>
								<div 
									class="entity-empty-state entity-empty-state--secondary"
									style="display: none;"
								>
									<div class="icon">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
										</svg>
									</div>
									<span>No parameters set</span>
									<button
										class="action"
										type="button"
										onclick="addParamOnClick(this);"
									>
										Add parameter
									</button>
								</div>
								<fieldset class="param-box__inputs" disabled>
									<div class="param-box__list">
										<div class="param-box__item">
											<input name="form-key" required placeholder="Key" />
											<input name="form-value" required placeholder="Value" />
											<button type="button" onclick="removeParamOnClick(this);">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
													<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
												</svg>
											</button>
										</div>
									</div>
									<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
										<div>
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
												<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
											</svg>
										</div>
										<span>Add parameter</span>
									</button>
								</fieldset>
							</fieldset>
						</div>

						<div
							id="notification-channels"
							class="notification-channels"
							{{if eq .RefreshID "notification-channels"}}hx-swap-oob="true"{{end}}
						>
							<label>
								<span>Notification channels</span>
							</label>

							{{if not (len .Notifications)}}
								<div
									class="entity-empty-state entity-empty-state--secondary" 
									style="margin-top: 1.0rem;"
								>
									<div class="icon">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
											<path fill-rule="evenodd" d="M10 2a6 6 0 0 0-6 6c0 1.887-.454 3.665-1.257 5.234a.75.75 0 0 0 .515 1.076 32.91 32.91 0 0 0 3.256.508 3.5 3.5 0 0 0 6.972 0 32.903 32.903 0 0 0 3.256-.508.75.75 0 0 0 .515-1.076A11.448 11.448 0 0 1 16 8a6 6 0 0 0-6-6ZM8.05 14.943a33.54 33.54 0 0 0 3.9 0 2 2 0 0 1-3.9 0Z" clip-rule="evenodd" />
										</svg> 
									</div>
									<span>No notification channels found</span>
									<div class="actions">
										<a class="action" href="/admin/notifications/create" target="_blank">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
												<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
												<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
											</svg>
											Add channel
										</a>
										<button type="button" class="empty-state-refresh" hx-get="?refresh=notification-channels">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
												<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
											</svg>
											Refresh
										</button>
									</div>
								</div>
							{{end}}

							<div class="notification-channels-group">
								{{range $notification := .Notifications}}
									<label>
										<input type="checkbox" name="notification-channels" value="{{$notification.ID}}" />
										<span>
											{{if eq $notification.Type "smtp"}}
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
													<path d="M3 4a2 2 0 00-2 2v1.161l8.441 4.221a1.25 1.25 0 001.118 0L19 7.162V6a2 2 0 00-2-2H3z" />
													<path d="M19 8.839l-7.77 3.885a2.75 2.75 0 01-2.46 0L1 8.839V14a2 2 0 002 2h14a2 2 0 002-2V8.839z" />
												</svg>
											{{else if eq $notification.Type "slack"}}
												<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
													<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
													<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
													<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
													<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
													<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
													<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
													<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
													<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
												</svg>
											{{end}}
											{{$notification.Name}}
										</span>
									</label>
								{{end}}
							</div>
						</div>

						<fieldset 
							id="notification-mail-groups"
							class="notification-mail-groups"
							{{if eq .RefreshID "notification-mail-groups"}}hx-swap-oob="true"{{end}}
						>
							<legend>
								Mail groups
							</legend>

							{{if not (len .MailGroups)}}
								<div
									class="entity-empty-state entity-empty-state--secondary" 
									style="margin-top: 1.0rem;"
								>
									<div class="icon">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
											<path d="M3 4a2 2 0 0 0-2 2v1.161l8.441 4.221a1.25 1.25 0 0 0 1.118 0L19 7.162V6a2 2 0 0 0-2-2H3Z" />
											<path d="m19 8.839-7.77 3.885a2.75 2.75 0 0 1-2.46 0L1 8.839V14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2V8.839Z" />
										</svg>  
									</div>
									<span>
										No mail groups found
									</span>
									<div class="actions">
										<a class="action" href="/admin/notifications/mail-groups/create" target="_blank">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
												<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
												<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
											</svg>
											Add mail group
										</a>
										<button type="button" class="empty-state-refresh" hx-get="?refresh=notification-mail-groups">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
												<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
											</svg>
											Refresh
										</button>
									</div>
								</div>
							{{end}}

							<div class="notification-mail-groups-group">
								{{range $mailGroup := .MailGroups}}
									<label>
										<input 
											type="checkbox"
											name="mail-groups"
											value="{{$mailGroup.ID}}"
										/>
										<span>
											<span>
												{{$mailGroup.Name}}
											</span>
											<span>
												{{$mailGroup.Description}}
											</span>
										</span>
									</label>
								{{end}}
							</div>
						</fieldset>

						<div>
							<button type="submit">Create</button>
						</div>

						<link
							rel="stylesheet"
							data-name="vs/editor/editor.main"
							href="/static/monaco-editor/min/vs/editor/editor.main.css"
						/>
			
						<script>
							var require = { paths: { vs: '/static/monaco-editor/min/vs' } };
						</script>
						
						<script>
							function addParamOnClick(e) {
								const root = e.closest(".param-box");

								const paramBoxInputs = root.querySelector(".param-box__inputs");

								if (paramBoxInputs.disabled) {
									paramBoxInputs.disabled = false;
									root.querySelector(".entity-empty-state").style.display = "none";
									return;
								}

								const items = root.querySelectorAll(".param-box__item")

								const clone = items[0].cloneNode(true);

								const paramBoxList = root.querySelector(".param-box__list")
										
								const insertedClone = paramBoxList.appendChild(
									clone,
								);

								insertedClone.querySelectorAll("input").forEach(v => {
									v.value = "";
								});
							}
							
							function removeParamOnClick(e) {
								const root = e.closest(".param-box");

								const paramBoxInputs = root.querySelector(".param-box__inputs");
								
								const items = paramBoxInputs.querySelectorAll(".param-box__item");
								if (items.length === 1) {								
									const emptyState = root.querySelector(".entity-empty-state");
									emptyState.style.display = "flex";
									root.querySelector(".param-box__inputs").disabled = true;
									[...root.querySelectorAll("input")].forEach(v => v.value = "");
								} else {
									e.parentElement.remove();
								}
							}

							function handleFormatChange(e) {
								const form = e.closest("form");
								
								const format = e.value;

								const editorContainer = document.getElementById("editor-container");
								const paramBox = document.querySelector("#body-param-box");

								if (format === "form") {
									e.form.elements["body"].disabled = true;
									editorContainer.style.display = "none";
									paramBox.style.display = "block";
									paramBox.disabled = false;
									if (format === "form") {
										if (
											form.elements["form-key"].value ||
											form.elements["form-value"].value ||
											form.elements["form-key"].length
										) {
											paramBox.querySelector(".param-box__inputs").disabled = false;
										} else {
											paramBox.querySelector(".entity-empty-state").style.display = "flex";
										}
									}
								} else if (format === "text") {
									e.form.elements["body"].disabled = false;
									editorContainer.style.display = "block";
									paramBox.style.display = "none";
									paramBox.disabled = true;
									paramBox.querySelector(".param-box__inputs").disabled = true;
								}
							}

							function handleMethodChange(e) {
								const form = e.closest("form");

								const format = form.elements["format"];

								const bodyContainer = document.querySelector("#request-body-container");

								const paramBox = document.querySelector("#body-param-box");

								if (["GET", "DELETE"].includes(e.value)) {
									bodyContainer.style.display = "none";
									form.elements["format"].forEach(v => {
										v.disabled = true;
									});
									paramBox.querySelector(".param-box__inputs").disabled = true;
									form.elements["body"].disabled = true;	
								}

								if (["POST", "PATCH", "PUT"].includes(e.value)) {
									bodyContainer.style.display = "block";
									form.elements["format"].forEach(v => {
										v.disabled = false;
									});
									if (format.value === "form") {
										if (
											form.elements["form-key"].value ||
											form.elements["form-value"].value ||
											form.elements["form-key"].length
										) {
										paramBox.querySelector(".param-box__inputs").disabled = false;
										} else {
										paramBox.querySelector(".entity-empty-state").style.display = "flex";
										}
									}
									form.elements["body"].disabled = format.value !== "text";
								}
							}

							(async () => {
								function addScript(url) {
									return new Promise((resolve, reject) => {
										const script = document.createElement('script');
										script.onload = () => {
											resolve();
										};
										script.onerror = reject;
										script.src = url;
										document.body.appendChild(script);
									});
								}

								const form = document.querySelector("form");

								if (window.monaco) {
									window.monaco.editor.getModels().forEach(model => model.dispose());
									initEditor();
								}

								function initEditor() {
									const editor = monaco.editor.create(document.getElementById("editor-container"), {
										language: 'json',
										fontSize: 16,
										theme: "vs-dark",
										minimap: {enabled: false},
										overviewRulerLanes: 0,
										padding: {top: 24},
										automaticLayout: true,
									});	
																		
									editor.getModel().onDidChangeContent((event) => {
										form.elements["body"].value = editor.getModel().getValue();
									});
								}

								if (!window.monaco) {
									await addScript("/static/monaco-editor/min/vs/loader.js");
									await addScript("/static/monaco-editor/min/vs/editor/editor.main.nls.js");
									await addScript("/static/monaco-editor/min/vs/editor/editor.main.js");
									initEditor();
								}
							})();
						</script>
					</form>
				</div>
			{{end}}
		`

	tmpl, err := parseTmpl("getCreateMonitor", markup)
	if err != nil {
		log.Printf("getCreateMonitor.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Notifications []NotificationChannel
			MailGroups    []MailGroup
			RefreshID     string
			Ctx           pageCtx
		}{
			Notifications: notifications,
			MailGroups:    mailGroups,
			RefreshID:     refreshID,
			Ctx:           getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getCreateMonitor.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func updateMonitorNotificationChannels(tx *sql.Tx, monitorID int, channelIDs []int) error {
	const deleteQuery = `
		delete from monitor_notification_channel where monitor_id = ?
	`

	_, err := tx.Exec(deleteQuery, monitorID)
	if err != nil {
		return fmt.Errorf("updateMonitorNotificationChannels.DeleteExec: %w", err)
	}

	if len(channelIDs) > 0 {
		const baseInsertQuery = `
			insert into monitor_notification_channel(monitor_id, notification_channel_id)
			values
		`

		insertQuery := baseInsertQuery

		for i := range channelIDs {
			insertQuery += "(?, ?)"

			if i != len(channelIDs)-1 {
				insertQuery += ","
			}
		}

		params := []any{}
		for _, v := range channelIDs {
			params = append(params, monitorID, v)
		}

		_, err = tx.Exec(insertQuery, params...)
		if err != nil {
			return fmt.Errorf("updateMonitorNotificationChannels.InsertExec: %w", err)
		}
	}

	return nil
}

func createMonitor(
	tx *sql.Tx,
	name string,
	url string,
	method string,
	frequency int,
	timeout int,
	attempts int,
	requestHeaders sql.NullString,
	bodyFormat sql.NullString,
	body sql.NullString,
) (int, error) {
	const query = `
		insert into
			monitor(name, url, method, frequency, timeout, attempts, request_headers, 
				body_format, body)
			values(?, ?, ?, ?, ?, ?, ?, ?, ?) returning id
	`

	var monitorID int
	err := tx.QueryRow(
		query,
		name,
		url,
		method,
		frequency,
		timeout,
		attempts,
		requestHeaders,
		bodyFormat,
		body,
	).Scan(&monitorID)
	if err != nil {
		return monitorID, fmt.Errorf("createMonitor.QueryRow: %w", err)
	}

	return monitorID, nil
}

func postCreateMonitor(w http.ResponseWriter, r *http.Request) {
	name := r.PostFormValue("name")
	if name == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	reqURL := r.PostFormValue("url")
	validURL := true
	parsedReqURL, err := url.Parse(reqURL)
	if err != nil {
		validURL = false
	} else if parsedReqURL.Scheme == "" || parsedReqURL.Host == "" {
		validURL = false
	} else if parsedReqURL.Scheme != "http" && parsedReqURL.Scheme != "https" {
		validURL = false
	}

	if !validURL {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<span id="alert-error" hx-swap-oob="true">
				Invalid URL
			</span>
		`))
		return
	}

	method := r.PostFormValue("method")
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if method != http.MethodGet &&
		method != http.MethodPost &&
		method != http.MethodPatch &&
		method != http.MethodPut &&
		method != http.MethodDelete {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	frequency, err := strconv.Atoi(r.PostFormValue("frequency"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if frequency != 10 && frequency != 30 && frequency != 60 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	timeout, err := strconv.Atoi(r.PostFormValue("timeout"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if timeout != 5 && timeout != 10 && timeout != 15 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	attempts, err := strconv.Atoi(r.PostFormValue("attempts"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if attempts != 1 && attempts != 2 && attempts != 3 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	requestHeaders := sql.NullString{}
	requestHeadersMap := map[string]string{}
	if r.PostFormValue("header-key") != "" && r.PostFormValue("header-value") != "" {
		for i := range r.Form["header-key"] {
			requestHeadersMap[r.Form["header-key"][i]] = r.Form["header-value"][i]
		}
	}
	requestHeadersSerialized, err := json.Marshal(requestHeadersMap)
	if err != nil {
		log.Printf("postEditMonitor.Marshal: %s", err)
		w.WriteHeader(http.StatusBadRequest)
		return
	}
	if len(requestHeadersMap) > 0 {
		requestHeaders = sql.NullString{
			Valid:  true,
			String: string(requestHeadersSerialized),
		}
	}

	body := sql.NullString{}
	if r.PostFormValue("body") != "" {
		body = sql.NullString{
			Valid:  true,
			String: r.PostFormValue("body"),
		}
	}

	if r.PostFormValue("form-key") != "" && r.PostFormValue("form-value") != "" {
		urlValues := url.Values{}
		for i := 0; i < len(r.Form["form-key"]); i++ {
			urlValues.Add(r.Form["form-key"][i], r.Form["form-value"][i])
		}
		body = sql.NullString{
			Valid:  true,
			String: urlValues.Encode(),
		}
	}

	format := sql.NullString{}
	if r.PostFormValue("format") != "" {
		format = sql.NullString{
			Valid:  true,
			String: r.PostFormValue("format"),
		}
	}

	notificationChannelsParam := r.PostForm["notification-channels"]
	notificationChannels := make([]int, 0, len(notificationChannelsParam))
	for _, channelID := range notificationChannelsParam {
		id, err := strconv.Atoi(channelID)
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		notificationChannels = append(notificationChannels, id)
	}

	mailGroupsParam := r.PostForm["mail-groups"]
	mailGroups := make([]int, 0, len(mailGroupsParam))
	for _, channelID := range mailGroupsParam {
		id, err := strconv.Atoi(channelID)
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		mailGroups = append(mailGroups, id)
	}
	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postCreateMonitor.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	monitorID, err := createMonitor(
		tx,
		name,
		reqURL,
		method,
		frequency,
		timeout,
		attempts,
		requestHeaders,
		format,
		body,
	)
	if err != nil {
		log.Printf("postCreateMonitor.createMonitor: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMonitorNotificationChannels(tx, monitorID, notificationChannels)
	if err != nil {
		log.Printf("postCreateMonitor.updateMonitorNotificationChannels: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMonitorMailGroups(tx, monitorID, mailGroups)
	if err != nil {
		log.Printf("postEditMonitor.updateMonitorMailGroups: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postCreateMonitor.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/monitors/"+strconv.Itoa(monitorID))
}

type AlertDetailMessage struct {
	ID            int
	Content       string
	CreatedAt     *time.Time
	LastUpdatedAt *time.Time
}

type AlertDetailService struct {
	ID         int
	Name       string
	HelperText string
}

type AlertDetail struct {
	ID        int
	Title     string
	AlertType string
	Severity  string
	CreatedAt *time.Time
	EndedAt   *time.Time
	Messages  []AlertDetailMessage
	Services  []AlertDetailService
}

func getAlertByID(tx *sql.Tx, id int) (AlertDetail, error) {
	const alertQuery = `
		select 
			id,
			title,
			type,
			severity,
			created_at,
			ended_at
		from
			alert
		where
			id = ?
	`

	alert := AlertDetail{}

	err := tx.QueryRow(alertQuery, id).Scan(
		&alert.ID,
		&alert.Title,
		&alert.AlertType,
		&alert.Severity,
		&alert.CreatedAt,
		&alert.EndedAt,
	)
	if err != nil {
		return alert, fmt.Errorf("getAlertByID.QueryRow: %w", err)
	}

	const messageQuery = `
		select
			id,
			content,
			created_at,
			last_updated_at
		from
			alert_message
		where
			alert_id = ?
		order by created_at desc
	`

	rows, err := tx.Query(messageQuery, id)
	if err != nil {
		return alert, fmt.Errorf("getAlertByID.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		message := AlertDetailMessage{}
		err = rows.Scan(
			&message.ID,
			&message.Content,
			&message.CreatedAt,
			&message.LastUpdatedAt,
		)
		if err != nil {
			return alert, fmt.Errorf("getAlertByID.Scan: %w", err)
		}

		alert.Messages = append(alert.Messages, message)
	}

	const serviceQuery = `
		select
			service.id,
			service.name,
			service.helper_text
		from
			alert_service
		left join
			service on service.id = alert_service.service_id
		where
			alert_id = ?
	`

	rows, err = tx.Query(serviceQuery, id)
	if err != nil {
		return alert, fmt.Errorf("getAlertByID.Query2: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		service := AlertDetailService{}
		err = rows.Scan(
			&service.ID,
			&service.Name,
			&service.HelperText,
		)
		if err != nil {
			return alert, fmt.Errorf("getAlertByID.Scan2: %w", err)
		}

		alert.Services = append(alert.Services, service)
	}

	return alert, nil
}

type AlertSettings struct {
	SlackInstallURL      string
	SlackClientSecret    string
	ManagedSubscriptions bool
}

func getAlertSettings(tx *sql.Tx) (AlertSettings, error) {
	const query = `
		select name, value from alert_setting
	`

	settings := AlertSettings{}

	rows, err := tx.Query(query)
	if err != nil {
		return settings, fmt.Errorf("getAlertSettings.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var k, v string

		err = rows.Scan(&k, &v)
		if err != nil {
			return settings, fmt.Errorf("getAlertSettings.Scan: %w", err)
		}

		if k == "slack-install-url" {
			settings.SlackInstallURL = v
		} else if k == "slack-client-secret" {
			settings.SlackClientSecret = v
		} else if k == "managed-subscriptions" {
			parsedV, err := strconv.ParseBool(v)
			if err != nil {
				return settings, fmt.Errorf("getAlertSettings.ParseBool: %w", err)
			}
			settings.ManagedSubscriptions = parsedV
		}
	}

	return settings, nil
}

func getAlertSMTPNotificationSetting(tx *sql.Tx) (int, error) {
	const query = `
		select notification_channel_id from alert_setting_smtp_notification limit 1
	`

	v := 0

	err := tx.QueryRow(query).Scan(&v)
	if err != nil {
		return v, fmt.Errorf("getAlertSMTPNotificationSetting.QueryRow: %w", err)
	}

	return v, nil
}

func getAlertNotifications(w http.ResponseWriter, r *http.Request) {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("getAlertNotifications.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	notifications, err := listNotificationChannels(tx, listNotificationsOptions{Type: "smtp"})
	if err != nil {
		log.Printf("getAlertNotifications.listNotificationChannels: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	settings, err := getAlertSettings(tx)
	if err != nil {
		log.Printf("getAlertNotifications.getAlertSettings: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	smtpNotificationChannelID, err := getAlertSMTPNotificationSetting(tx)
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Printf("getAlertNotifications.getAlertSMTPNotificationSetting: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getAlertNotifications.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Alert notifications{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/alerts" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
				
						<h2>Alert notifications</h2>
					</div>
				</div>

				<p style="font-size: 1.6rem; margin-bottom: 4.6rem;">Configure which options appear on your status page for visitors to receive alert updates</p>
				
				<form hx-post hx-swap="none" autocomplete="off">
					<div class="notification-channels">
						<label>
							Email notification channel
							<span class="subtext">
								Choose a notification channel to use for status page email alerts
							</span>
						</label>

						<div 
							id="notification-channels-group"
							class="notification-channels-group"
							{{if and .Ctx.HXRequest (not .Ctx.HXBoosted)}}hx-swap-oob="true"{{end}}
						>
							{{if not (len .Notifications)}}
								<div
									class="entity-empty-state entity-empty-state--secondary" 
									style="width: 100%; margin-top: 1.0rem;"
								>
									<div class="icon">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
											<path d="M3 4a2 2 0 0 0-2 2v1.161l8.441 4.221a1.25 1.25 0 0 0 1.118 0L19 7.162V6a2 2 0 0 0-2-2H3Z" />
											<path d="m19 8.839-7.77 3.885a2.75 2.75 0 0 1-2.46 0L1 8.839V14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2V8.839Z" />
										</svg>  
									</div>
									<span>No email notification channels found</span>
									<div class="actions">
										<a 
											class="action"
											href="/admin/notifications/create"
											target="_blank"
											hx-boost="true"
											hx-swap="outerHTML"
										>
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
												<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
												<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
											</svg>
											Add channel
										</a>
										<button type="button" class="empty-state-refresh" hx-get="">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
												<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
											</svg>
											Refresh
										</button>
									</div>
								</div>
							{{end}}
							{{range $notification := .Notifications}}
								<label>
									<input
										type="checkbox"
										name="smtp-notification-channel"
										value="{{$notification.ID}}"
										onchange="onChangeChannel(this)"
										{{if eq $notification.ID $.SMTPNotificationChannel}}checked{{end}}
									/>
									<span>
										{{$notification.Name}}
									</span>
								</label>
							{{end}}
						</div>
					</div>

					<label>
						Statusnook managed unsubscribe
						<span class="subtext">
							Disable this option if you want to use your mail providers unsubscribe links
						</span>
						<span class="subtext">
							We currently recommend that only Postmark users turn this off
						</span>
					</label>

					<div class="checkbox-group">
						<label>
							<input 
								name="managed-subscriptions"
								type="checkbox"
								{{if $.Settings.ManagedSubscriptions}}checked{{end}}
							/>
						</label>
					</div>


					<hr style="border: 1px solid #F6F6F6; margin-top: 0; margin-bottom: 3.6rem;">

					<label>
						Slack client secret
						<span class="subtext">
							Paste the client secret for your Slack app
						</span>
						<input name="slack-client-secret" type="password" value="{{$.Settings.SlackClientSecret}}">
					</label>

					<label>
						Slack install URL
						<span class="subtext">
							Paste the shareable URL for your Slack app
						</span>
						<input name="slack-install-url" type="url" value="{{$.Settings.SlackInstallURL}}">
					</label>

					<div class="slack-container" style="display: block;">

						<a 
							class="help"
							href="https://api.slack.com/apps"
							target="_blank"
						>
							Go to your Slack apps
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
								<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
								<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
							</svg>

						</a>

						<button 
							type="button"
							class="help"
							onclick="document.querySelector('.slack-tutorial').classList.toggle('slack-tutorial--visible');"
						>
							How do I create a Slack app?
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
								<path fill-rule="evenodd" d="M4.22 6.22a.75.75 0 0 1 1.06 0L8 8.94l2.72-2.72a.75.75 0 1 1 1.06 1.06l-3.25 3.25a.75.75 0 0 1-1.06 0L4.22 7.28a.75.75 0 0 1 0-1.06Z" clip-rule="evenodd" />
							</svg>
						</button>

						<div class="slack-tutorial">
							<a href="https://api.slack.com/apps/new" target="_blank">
								<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
									<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
									<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
									<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
									<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
									<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
									<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
									<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
									<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
								</svg>
								Create new Slack app
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
									<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
									<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
								</svg>
							</a>

							<p>Select the "From scratch" option</p>
							<img 
								src="/static/images/slack-notification-tutorial/1.png"
								style="width: 60%;"
							/>

							<p>Name your app, choose your Slack workspace, and click “Create app”</p>
							<img 
								src="/static/images/slack-notification-tutorial/2.png"
								style="width: 60%;"
							/>
						</div>

						<button 
							type="button"
							class="help"
							onclick="document.querySelector('.slack-tutorial-app').classList.toggle('slack-tutorial-app--visible');"
						>
							How do I configure my Slack app for status page alerts?
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
								<path fill-rule="evenodd" d="M4.22 6.22a.75.75 0 0 1 1.06 0L8 8.94l2.72-2.72a.75.75 0 1 1 1.06 1.06l-3.25 3.25a.75.75 0 0 1-1.06 0L4.22 7.28a.75.75 0 0 1 0-1.06Z" clip-rule="evenodd" />
							</svg>
						</button>

						<div class="slack-tutorial-app">
							<p>Turn incoming webhooks on - you don't need to add any webhooks</p>
							<img
								src="/static/images/slack-notification-tutorial/configure-1.png"
								style="width: 100%;"
							/>

							<p>
								Add the following redirect URL to your Slack app:
								https://{{.Domain}}/callback/slack
							</p>
							<img 
								src="/static/images/slack-notification-tutorial/configure-2.png"
								style="width: 100%;"
							/>

							<p>Copy the client secret and paste it into Statusnook</p>
							<img 
								src="/static/images/slack-notification-tutorial/configure-3.png"
								style="width: 100%;"
							/>

							<p>Copy the sharable URL and paste it into Statusnook</p>
							<img 
								src="/static/images/slack-notification-tutorial/configure-4.png"
								style="width: 100%;"
							/>
						</div>
					</div>
					
					<div>
						<button type="submit">Confirm</button>
					</div>
				</form>
			</div>
			<script>
				function onChangeChannel(e) {
					const form = e.closest("form");

					form.elements["smtp-notification-channel"].forEach(v => {
						if (v !== e) {
							v.checked = false;
						}
					});
				}
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getAlertNotifications", markup)
	if err != nil {
		log.Printf("getAlertNotifications.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(w, struct {
		Notifications           []NotificationChannel
		Settings                AlertSettings
		SMTPNotificationChannel int
		Domain                  string
		Ctx                     pageCtx
	}{
		Notifications:           notifications,
		Settings:                settings,
		SMTPNotificationChannel: smtpNotificationChannelID,
		Domain:                  metaDomain,
		Ctx:                     getPageCtx(r),
	})
	if err != nil {
		log.Printf("getAlertNotifications.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func updateAlertSettings(
	tx *sql.Tx,
	slackInstallURL string,
	slackClientSecret string,
	managedSubscriptions bool,
) error {
	const query = `
		insert into alert_setting(name, value) values(?, ?), (?, ?), (?, ?)
		on conflict(name) do update set value = excluded.value
	`

	_, err := tx.Exec(
		query,
		"slack-install-url",
		slackInstallURL,
		"slack-client-secret",
		slackClientSecret,
		"managed-subscriptions",
		managedSubscriptions,
	)
	if err != nil {
		return fmt.Errorf("updateAlertSettings.Exec: %w", err)
	}

	return nil
}

func updateAlertSMTPNotificationSetting(tx *sql.Tx, notificationID int) error {
	const deleteQuery = `
		delete from alert_setting_smtp_notification
	`

	_, err := tx.Exec(deleteQuery)
	if err != nil {
		return fmt.Errorf("updateAlertSMTPNotificationSetting.ExecDelete: %w", err)
	}

	if notificationID != 0 {
		const insertQuery = `
			insert into alert_setting_smtp_notification(notification_channel_id) values(?)
		`

		_, err = tx.Exec(insertQuery, notificationID)
		if err != nil {
			return fmt.Errorf("updateAlertSMTPNotificationSetting.ExecInsert: %w", err)
		}
	}

	return nil
}

func postAlertNotifications(w http.ResponseWriter, r *http.Request) {
	slackInstallURLParam := r.FormValue("slack-install-url")
	slackInstallURL := ""
	if slackInstallURLParam != "" {
		url, err := url.ParseRequestURI(slackInstallURLParam)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		slackInstallURL = url.String()
	}

	slackClientSecretParam := r.FormValue("slack-client-secret")

	smtpNotificationChannelIDParam := r.FormValue("smtp-notification-channel")
	smtpNotificationChannelID := 0
	if smtpNotificationChannelIDParam != "" {
		id, err := strconv.Atoi(r.FormValue("smtp-notification-channel"))
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		smtpNotificationChannelID = id
	}

	managedSubscriptions := false
	managedSubscriptionsParam := r.FormValue("managed-subscriptions")
	if managedSubscriptionsParam == "on" {
		managedSubscriptions = true
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postAlertNotifications.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	channel, err := getNotificationChannelByID(tx, smtpNotificationChannelID)
	if err != nil && !errors.Is(err, sql.ErrNoRows) {
		log.Printf("postAlertNotifications.getNotificationChannelByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if channel.ID != 0 && channel.Type != "smtp" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	err = updateAlertSMTPNotificationSetting(tx, channel.ID)
	if err != nil {
		log.Printf("postAlertNotifications.updateAlertSMTPNotificationSetting: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateAlertSettings(tx, slackInstallURL, slackClientSecretParam, managedSubscriptions)
	if err != nil {
		log.Printf("postAlertNotifications.updateAlertSettings: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postAlertNotifications.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts")
}

func getAlert(w http.ResponseWriter, r *http.Request) {
	idParam := chi.URLParam(r, "id")

	id, err := strconv.Atoi(idParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	alert, err := getAlertByID(tx, id)
	if err != nil {
		log.Printf("getAlert.getAlertByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("getAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}{{.Alert.Title}} - Alert{{end}}
		{{define "body"}}
			<div class="alert-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/alerts" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
						{{if not .Alert.EndedAt }}
							{{if eq .Alert.AlertType "incident"}}
								<div class="live">LIVE</div>
							{{else}}
								<div class="active">ACTIVE</div>
							{{end}}
						{{end}}
						<h2>{{.Alert.Title}}</h2>
					</div>
					<div>
						<div class="menu">
							<button class="menu-button">
								<svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 12 12" fill="none">
									<path d="M5.99961 1.80005C6.2383 1.80005 6.46722 1.89487 6.63601 2.06365C6.80479 2.23244 6.89961 2.46135 6.89961 2.70005C6.89961 2.93874 6.80479 3.16766 6.63601 3.33645C6.46722 3.50523 6.2383 3.60005 5.99961 3.60005C5.76091 3.60005 5.532 3.50523 5.36321 3.33645C5.19443 3.16766 5.09961 2.93874 5.09961 2.70005C5.09961 2.46135 5.19443 2.23244 5.36321 2.06365C5.532 1.89487 5.76091 1.80005 5.99961 1.80005ZM5.99961 5.10005C6.2383 5.10005 6.46722 5.19487 6.63601 5.36365C6.80479 5.53244 6.89961 5.76135 6.89961 6.00005C6.89961 6.23874 6.80479 6.46766 6.63601 6.63645C6.46722 6.80523 6.2383 6.90005 5.99961 6.90005C5.76091 6.90005 5.532 6.80523 5.36321 6.63645C5.19443 6.46766 5.09961 6.23874 5.09961 6.00005C5.09961 5.76135 5.19443 5.53244 5.36321 5.36365C5.532 5.19487 5.76091 5.10005 5.99961 5.10005ZM6.89961 9.30005C6.89961 9.06135 6.80479 8.83244 6.63601 8.66365C6.46722 8.49487 6.2383 8.40005 5.99961 8.40005C5.76091 8.40005 5.532 8.49487 5.36321 8.66365C5.19443 8.83244 5.09961 9.06135 5.09961 9.30005C5.09961 9.53874 5.19443 9.76766 5.36321 9.93645C5.532 10.1052 5.76091 10.2 5.99961 10.2C6.2383 10.2 6.46722 10.1052 6.63601 9.93645C6.80479 9.76766 6.89961 9.53874 6.89961 9.30005Z" fill="#595959"/>
								</svg>
							</button>

							<dialog>
								{{if .Alert.EndedAt}}
									<button onclick="document.getElementById('unresolve-dialog').showModal();">Unresolve</button>
								{{else}}
									<button onclick="document.getElementById('resolve-dialog').showModal();">Resolve</button>
								{{end}}
								<a href="/admin/alerts/{{.Alert.ID}}/edit" hx-boost="true">Edit</a>
								<button onclick="document.getElementById('delete-dialog').showModal();">Delete</button>
							</dialog>
						</div>

						<dialog class="modal" id="resolve-dialog">
							<span>Resolve {{.Alert.Title}}</span>
							<form hx-post="/admin/alerts/{{.Alert.ID}}/resolve" hx-swap="none">
								<div>
									<button onclick="document.getElementById('resolve-dialog').close(); return false;">Cancel</button>
									<button><span></span>Resolve</button>
								</div>
							</form>
					 	</dialog>

						<dialog class="modal" id="unresolve-dialog">
							<span>Unresolve {{.Alert.Title}}</span>
							<form hx-post="/admin/alerts/{{.Alert.ID}}/unresolve" hx-swap="none">
								<div>
									<button onclick="document.getElementById('unresolve-dialog').close(); return false;">Cancel</button>
									<button><span></span>Unresolve</button>
								</div>
							</form>
					  	</dialog>

						<dialog class="modal" id="delete-dialog">
							<span>Delete {{.Alert.Title}}</span>
							<form hx-delete hx-swap="none">
								<div>
									<button onclick="document.getElementById('delete-dialog').close(); return false;">Cancel</button>
									<button><span></span>Delete</button>
								</div>
							</form>
					 	</dialog>
					</div>
				</div>
				<div class="alert-services">
					<h2>Affected services</h2>
					<div>
						<span>{{.Services}}</span>
					</div>
				</div>
				<div class="alert-container-messages">
					<div>
						<h2>Timeline</h2>
						<div>
							<a href="/admin/alerts/{{.Alert.ID}}/messages" hx-boost="true">
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
									<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
								</svg>
							</a>
						</div>
					</div>
					<div>
						{{range $message := .Alert.Messages}}
							<div>
								<div>
									<span>{{$message.CreatedAt}}</span>
									<div>
										<div class="menu">
											<button class="menu-button">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
													<path d="M3 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM8.5 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM15.5 8.5a1.5 1.5 0 100 3 1.5 1.5 0 000-3z" />
												</svg>
											</button>

											<dialog class="message-menu-options">
												<a href="/admin/alerts/{{$.Alert.ID}}/messages/{{$message.ID}}" hx-boost="true">Edit</a>
												<button onclick="document.getElementById('delete-message-{{$message.ID}}').showModal();">Delete</button>
											</dialog>
										</div>

										<dialog class="modal" id="delete-message-{{$message.ID}}">
											<span>Delete message</span>
											<form hx-delete="/admin/alerts/{{$.Alert.ID}}/messages/{{$message.ID}}" hx-swap="none">
												<div>
													<button onclick="document.getElementById('delete-message-{{$message.ID}}').close(); return false;">Cancel</button>
													<button><span></span>Delete</button>
												</div>
											</form>
					 					</dialog>
									</div>
								</div>
								<span>{{$message.Content}}</span>
							</div>
						{{end}}
					</div>
				</div>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getAlert", markup)
	if err != nil {
		log.Printf("getAlert.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	type FormattedAlertDetailMessage struct {
		ID            int
		Content       string
		CreatedAt     string
		LastUpdatedAt string
	}

	type FormattedAlertDetailService struct {
		ID         int
		Name       string
		HelperText string
	}

	type FormattedAlertDetail struct {
		ID        int
		Title     string
		AlertType string
		Severity  string
		CreatedAt string
		EndedAt   string
		Messages  []FormattedAlertDetailMessage
		Services  []FormattedAlertDetailService
	}

	formattedAlert := FormattedAlertDetail{}
	formattedAlert.ID = alert.ID
	formattedAlert.Title = alert.Title
	formattedAlert.AlertType = alert.AlertType
	formattedAlert.Severity = alert.Severity
	formattedAlert.CreatedAt = alert.CreatedAt.Format("02/01/2006 15:04 MST")
	if alert.EndedAt != nil {
		formattedAlert.EndedAt = alert.EndedAt.Format("02/01/2006 15:04 MST")
	}

	for _, message := range alert.Messages {
		createdAt := message.CreatedAt.Format("Jan 2 2006 • 15:04 MST")
		if message.CreatedAt.Year() == time.Now().UTC().Year() {
			createdAt = message.CreatedAt.Format("Jan 2 • 15:04 MST")
		}

		formattedMessage := FormattedAlertDetailMessage{
			ID:        message.ID,
			Content:   message.Content,
			CreatedAt: createdAt,
		}
		if message.LastUpdatedAt != nil {
			formattedMessage.LastUpdatedAt = message.LastUpdatedAt.Format("02/01/2006 15:04 MST")
		}

		formattedAlert.Messages = append(
			formattedAlert.Messages,
			formattedMessage,
		)
	}

	serviceNames := make([]string, 0, len(alert.Services))
	for _, service := range alert.Services {
		serviceNames = append(serviceNames, service.Name)
	}

	err = tmpl.Execute(
		w,
		struct {
			Alert    FormattedAlertDetail
			Services string
			Ctx      pageCtx
		}{
			Alert:    formattedAlert,
			Services: strings.Join(serviceNames, " • "),
			Ctx:      getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getAlert.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func deleteAlertByID(tx *sql.Tx, id int) error {
	const query = `
		delete from alert where id = ?
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("deleteAlertByID.Exec: %w", err)
	}

	return nil
}

func deleteAlert(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("deleteAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = deleteAlertByID(tx, id)
	if err != nil {
		log.Printf("deleteAlert.deleteAlertByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("deleteAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts")
}

func getCreateAlert(w http.ResponseWriter, r *http.Request) {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("getCreateAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	services, err := listServices(tx)
	if err != nil {
		log.Printf("getCreateAlert.listServices: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("getCreateAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Create alert{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/alerts" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						 </a>
				  
						<h2>Create alert</h2>
					</div>
				</div>

				<form hx-post hx-swap="none" autocomplete="off">
					<label>
						Title
						<input name="title" required />
					</label>

					<label>
						Messages
						<textarea name="message" required></textarea>
					</label>

					<div id="services" {{if and .Ctx.HXRequest (not .Ctx.HXBoosted)}}hx-swap-oob="true"{{end}}>
						<label>
							Affected services
						</label>

						{{if not (len .Services)}}
							<div
								class="entity-empty-state entity-empty-state--secondary" 
								style="margin-top: 1.0rem;"
							>
								<div class="icon">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
										<path d="M12 4.467c0-.405.262-.75.559-1.027.276-.257.441-.584.441-.94 0-.828-.895-1.5-2-1.5s-2 .672-2 1.5c0 .362.171.694.456.953.29.265.544.6.544.994a.968.968 0 0 1-1.024.974 39.655 39.655 0 0 1-3.014-.306.75.75 0 0 0-.847.847c.14.993.242 1.999.306 3.014A.968.968 0 0 1 4.447 10c-.393 0-.729-.253-.994-.544C3.194 9.17 2.862 9 2.5 9 1.672 9 1 9.895 1 11s.672 2 1.5 2c.356 0 .683-.165.94-.441.276-.297.622-.559 1.027-.559a.997.997 0 0 1 1.004 1.03 39.747 39.747 0 0 1-.319 3.734.75.75 0 0 0 .64.842c1.05.146 2.111.252 3.184.318A.97.97 0 0 0 10 16.948c0-.394-.254-.73-.545-.995C9.171 15.693 9 15.362 9 15c0-.828.895-1.5 2-1.5s2 .672 2 1.5c0 .356-.165.683-.441.94-.297.276-.559.622-.559 1.027a.998.998 0 0 0 1.03 1.005c1.337-.05 2.659-.162 3.961-.337a.75.75 0 0 0 .644-.644c.175-1.302.288-2.624.337-3.961A.998.998 0 0 0 16.967 12c-.405 0-.75.262-1.027.559-.257.276-.584.441-.94.441-.828 0-1.5-.895-1.5-2s.672-2 1.5-2c.362 0 .694.17.953.455.265.291.601.545.995.545a.97.97 0 0 0 .976-1.024 41.159 41.159 0 0 0-.318-3.184.75.75 0 0 0-.842-.64c-1.228.164-2.473.271-3.734.319A.997.997 0 0 1 12 4.467Z" />
									</svg>
								</div>
								<span>No services found</span>
								<div class="actions">
									<a class="action" href="/admin/services/create" target="_blank">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
											<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
										</svg>
										Add service
									</a>
									<button type="button" class="empty-state-refresh" hx-get="">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
										</svg>
										Refresh
									</button>
								</div>
							</div>
						{{end}}

						<div class="checkbox-group">
							{{range $service := .Services}}
								<label>
									<input
										name="services"
										type="checkbox"
										value="{{$service.ID}}"
										onchange="updateService();"
										required
									/>
									{{$service.Name}}
								</label>
							{{end}}
						</div>
					</div>

					<label>
						Type
					</label>
					<div class="checkbox-group">
						<label>
							<input 
								name="type" 
								type="radio"
								value="incident"
								onchange="updateType(this.value);"
							 	required
							/>
							Incident
						</label>
						<label>
							<input 
								name="type"
								type="radio"
								value="maintenance"
								onchange="updateType(this.value);"
								required
							/>
							Maintenance / notice
						</label>
					</div>

					<fieldset class="radio-group" style="display: none;" disabled>
						<legend>Severity</legend>
						<input name="severity" type="radio" value="red" required style="background-color: #E57F73;"/>
						<input name="severity" type="radio" value="amber" required style="background-color: #E5B773;"/>
					</fieldset>

					<div>
						<button type="submit">Create</button>
					</div>
				</form>
			</div>
			<script>
				function updateService() {
					const inputs = [...document.querySelectorAll("form [name='services']")];
					const anyChecked = inputs.some(e => e.checked); 

					[...document.querySelectorAll("form [name='services']")].forEach((e) => {
						e.required = !anyChecked;
					});
				}

				function updateType(type) {
					if (type === "incident") {
						document.querySelector(".radio-group").style.display = "block";
						document.querySelector(".radio-group").disabled = false;
					} else {
						document.querySelector(".radio-group").style.display = "none";
						document.querySelector(".radio-group").disabled = true;
					}
				}
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getCreateAlert", markup)
	if err != nil {
		log.Printf("getCreateAlert.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Services []service
			Ctx      pageCtx
		}{
			Services: services,
			Ctx:      getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getCreateAlert.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func createAlert(
	tx *sql.Tx,
	title string,
	services []int,
	alertType string,
	severity string,
) (int, error) {
	const alertQuery = `
		insert into alert(title, type, severity, created_at) values(?, ?, ?, ?) returning id
	`

	alertID := 0
	err := tx.QueryRow(alertQuery, title, alertType, severity, time.Now().UTC()).Scan(&alertID)
	if err != nil {
		return alertID, fmt.Errorf("createAlert.Scan: %w", err)
	}

	const baseServiceQuery = `
		insert into alert_service(alert_id, service_id) values
	`

	serviceQuery := baseServiceQuery

	params := []any{}

	for i, serviceID := range services {
		serviceQuery += "(?, ?)"
		if i < len(services)-1 {
			serviceQuery += ", "
		}
		params = append(params, alertID, serviceID)
	}

	_, err = tx.Exec(serviceQuery, params...)
	if err != nil {
		return alertID, fmt.Errorf("createAlert.Exec: %w", err)
	}

	return alertID, nil
}

func createAlertMessageNotifications(tx *sql.Tx, createdAt time.Time, alertMessageID int) error {
	const query = `
		insert into alert_notification(created_at, alert_subscription_id, alert_message_id)
		select ?, id, ? from alert_subscription where alert_subscription.active = true
	`

	_, err := tx.Exec(query, time.Now().UTC(), alertMessageID)
	if err != nil {
		return fmt.Errorf("createAlertMessageNotifications.Exec: %w", err)
	}

	return nil
}

func updateAlertSentAtByID(tx *sql.Tx, now time.Time, ids []int) error {
	const baseQuery = `
		update alert_notification set sent_at = ?
		where id in(
	`

	query := baseQuery

	params := []any{time.Now().UTC()}
	for i, destination := range ids {
		query += "?"
		if i < len(ids)-1 {
			query += ","
		}
		params = append(params, destination)
	}
	query += ")"

	_, err := tx.Exec(query, params...)
	if err != nil {
		return fmt.Errorf("updateAlertSentAtByID.Exec: %w", err)
	}

	return nil
}

func postCreateAlert(w http.ResponseWriter, r *http.Request) {
	title := r.PostFormValue("title")
	if title == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	message := r.PostFormValue("message")
	if message == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	services := []int{}
	for _, service := range r.PostForm["services"] {
		num, err := strconv.Atoi(service)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		services = append(services, num)
	}
	if len(services) == 0 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	alertType := r.PostFormValue("type")
	if alertType != "incident" && alertType != "maintenance" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	severity := r.PostFormValue("severity")
	if alertType == "incident" {
		if severity != "red" && severity != "amber" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
	} else {
		alertType = "maintenance"
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postCreateAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	alertID, err := createAlert(tx, title, services, alertType, severity)
	if err != nil {
		log.Printf("postCreateAlert.createAlert: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alertMessageID, err := createAlertMessage(tx, alertID, message)
	if err != nil {
		log.Printf("postCreateAlert.createAlertMessage: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alerts, err := getOngoingAlerts(tx)
	if err != nil {
		log.Printf("postCreateAlert.getOngoingAlerts: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	newSeverity := "blue"
	for _, alert := range alerts {
		if alert.Severity == "amber" {
			newSeverity = "amber"
			continue
		}

		if alert.Severity == "red" {
			newSeverity = "red"
			break
		}
	}

	err = updateSeverity(tx, newSeverity)
	if err != nil {
		log.Printf("postCreateAlert.updateSeverity: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = createAlertMessageNotifications(tx, time.Now().UTC(), alertMessageID)
	if err != nil {
		log.Printf("postCreateAlert.createAlertMessageNotifications: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postCreateAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts")
}

func getEditAlert(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getEditAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	services, err := listServices(tx)
	if err != nil {
		log.Printf("getEditAlert.listServices: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alert, err := getAlertByID(tx, id)
	if err != nil {
		log.Printf("getEditAlert.getAlertByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("getEditAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Edit alert{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/alerts/{{.Alert.ID}}" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
					
						<h2>Edit alert</h2>
					</div>
				</div>

				<form hx-post hx-swap="none" autocomplete="off">
					<label>
						Title
						<input name="title" value="{{.Alert.Title}}" required />
					</label>

					<div id="services" {{if and .Ctx.HXRequest (not .Ctx.HXBoosted)}}hx-swap-oob="true"{{end}}>
						<label>
							Affected services
						</label>

						{{if not (len .Services)}}
							<div
								class="entity-empty-state entity-empty-state--secondary" 
								style="margin-top: 1.0rem;"
							>
								<div class="icon">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
										<path d="M12 4.467c0-.405.262-.75.559-1.027.276-.257.441-.584.441-.94 0-.828-.895-1.5-2-1.5s-2 .672-2 1.5c0 .362.171.694.456.953.29.265.544.6.544.994a.968.968 0 0 1-1.024.974 39.655 39.655 0 0 1-3.014-.306.75.75 0 0 0-.847.847c.14.993.242 1.999.306 3.014A.968.968 0 0 1 4.447 10c-.393 0-.729-.253-.994-.544C3.194 9.17 2.862 9 2.5 9 1.672 9 1 9.895 1 11s.672 2 1.5 2c.356 0 .683-.165.94-.441.276-.297.622-.559 1.027-.559a.997.997 0 0 1 1.004 1.03 39.747 39.747 0 0 1-.319 3.734.75.75 0 0 0 .64.842c1.05.146 2.111.252 3.184.318A.97.97 0 0 0 10 16.948c0-.394-.254-.73-.545-.995C9.171 15.693 9 15.362 9 15c0-.828.895-1.5 2-1.5s2 .672 2 1.5c0 .356-.165.683-.441.94-.297.276-.559.622-.559 1.027a.998.998 0 0 0 1.03 1.005c1.337-.05 2.659-.162 3.961-.337a.75.75 0 0 0 .644-.644c.175-1.302.288-2.624.337-3.961A.998.998 0 0 0 16.967 12c-.405 0-.75.262-1.027.559-.257.276-.584.441-.94.441-.828 0-1.5-.895-1.5-2s.672-2 1.5-2c.362 0 .694.17.953.455.265.291.601.545.995.545a.97.97 0 0 0 .976-1.024 41.159 41.159 0 0 0-.318-3.184.75.75 0 0 0-.842-.64c-1.228.164-2.473.271-3.734.319A.997.997 0 0 1 12 4.467Z" />
									</svg>
								</div>
								<span>No services found</span>
								<div class="actions">
									<a class="action" href="/admin/services/create" target="_blank">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
											<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
										</svg>
										Add service
									</a>
									<button type="button" class="empty-state-refresh" hx-get="">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
										</svg>
										Refresh
									</button>
								</div>
							</div>
						{{end}}
						
						<div class="checkbox-group">
							{{range $service := .Services}}
								<label>
									<input 
										name="services" 
										{{if index $.CheckedServices $service.ID}}checked{{end}}
										type="checkbox"
										value="{{$service.ID}}"
										onchange="updateService();"
									/>
									{{$service.Name}}
								</label>
							{{end}}
						</div>
					</div>

					<label>
						Type
					</label>
					<div class="checkbox-group">
						<label>
							<input 
								name="type" 
								type="radio" 
								value="incident" 
								{{if eq .Alert.AlertType "incident"}}checked{{end}} 
								onchange="updateType(this.value);"
								required
							/>
							Incident
						</label>
						<label>
							<input 
								name="type"
								type="radio"
								value="maintenance"
								{{if eq .Alert.AlertType "maintenance"}}checked{{end}}
								onchange="updateType(this.value);"
								required
							/>
							Maintenance / notice
						</label>
					</div>

					<fieldset 
						class="radio-group"
						{{if ne .Alert.AlertType "incident"}}style="display: none;"{{end}}
						{{if ne .Alert.AlertType "incident"}}disabled{{end}}
					>
						<legend>Severity</legend>
						<input 
							name="severity"
							type="radio"
							value="red"
							{{if eq .Alert.Severity "red"}}checked{{end}}
							required
							style="background-color: #E57F73;"
						/>
						<input 
							name="severity"
							type="radio"
							value="amber"
							{{if eq .Alert.Severity "amber"}}checked{{end}}
							required 
							style="background-color: #E5B773;"
						/>
					</fieldset>

					<div>
						<button type="submit">Edit</button>
					</div>
				</form>
			</div>
			<script>
				function updateService() {
					const inputs = [...document.querySelectorAll("form [name='services']")];
					const anyChecked = inputs.some(e => e.checked); 

					[...document.querySelectorAll("form [name='services']")].forEach((e) => {
						e.required = !anyChecked;
					});
				}

				function updateType(type) {
					if (type === "incident") {
						document.querySelector(".radio-group").style.display = "block";
						document.querySelector(".radio-group").disabled = false;
					} else {
						document.querySelector(".radio-group").style.display = "none";
						document.querySelector(".radio-group").disabled = true;
					}
				}
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getEditAlert", markup)
	if err != nil {
		log.Printf("getEditAlert.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	checkedServices := map[int]bool{}
	for _, service := range services {
		checkedServices[service.ID] = false
	}
	for _, service := range alert.Services {
		checkedServices[service.ID] = true
	}

	err = tmpl.Execute(w, struct {
		Alert           AlertDetail
		Services        []service
		CheckedServices map[int]bool
		Ctx             pageCtx
	}{
		Alert:           alert,
		Services:        services,
		CheckedServices: checkedServices,
		Ctx:             getPageCtx(r),
	})
	if err != nil {
		log.Printf("getEditAlert.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func editAlert(
	tx *sql.Tx,
	id int,
	title string,
	services []int,
	alertType string,
	severity string,
) error {
	const alertQuery = `
		update alert set title = ?, type = ?, severity = ? where id = ?
	`

	_, err := tx.Exec(alertQuery, title, alertType, severity, id)
	if err != nil {
		return fmt.Errorf("editAlert.Exec: %w", err)
	}

	const serviceDeleteQuery = `
		delete from alert_service where alert_id = ?
	`

	_, err = tx.Exec(serviceDeleteQuery, id)
	if err != nil {
		return fmt.Errorf("editAlert.Exec2: %w", err)
	}

	const baseServiceInsertQuery = `
		insert into alert_service(alert_id, service_id) values
	`

	serviceInsertQuery := baseServiceInsertQuery

	params := []any{}

	for i, serviceID := range services {
		serviceInsertQuery += "(?, ?)"
		if i < len(services)-1 {
			serviceInsertQuery += ", "
		}
		params = append(params, id, serviceID)
	}

	_, err = tx.Exec(serviceInsertQuery, params...)
	if err != nil {
		return fmt.Errorf("editAlert.Exec3: %w", err)
	}

	return nil
}

func postEditAlert(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	title := r.PostFormValue("title")
	if title == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	services := []int{}
	for _, service := range r.PostForm["services"] {
		num, err := strconv.Atoi(service)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		services = append(services, num)
	}
	if len(services) == 0 {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	alertType := r.PostFormValue("type")
	if alertType != "incident" && alertType != "maintenance" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	severity := r.PostFormValue("severity")
	if alertType == "incident" {
		if severity != "red" && severity != "amber" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
	} else {
		alertType = "maintenance"
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postEditAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = editAlert(tx, id, title, services, alertType, severity)
	if err != nil {
		log.Printf("postEditAlert.editAlert: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alerts, err := getOngoingAlerts(tx)
	if err != nil {
		log.Printf("postEditAlert.getOngoingAlerts: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	newSeverity := "blue"
	for _, alert := range alerts {
		if alert.Severity == "amber" {
			newSeverity = "amber"
			continue
		}

		if alert.Severity == "red" {
			newSeverity = "red"
			break
		}
	}

	err = updateSeverity(tx, newSeverity)
	if err != nil {
		log.Printf("postEditAlert.updateSeverity: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postEditAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts")
}

func resolveAlert(tx *sql.Tx, id int) error {
	const query = `
		update alert set ended_at = ? where id = ?
	`

	_, err := tx.Exec(query, time.Now().UTC(), id)
	if err != nil {
		return fmt.Errorf("resolveAlert.Exec: %w", err)
	}

	return nil
}

func getSeverity(tx *sql.Tx) (string, error) {
	const query = `
		select severity from severity limit 1
	`

	var severity string

	err := tx.QueryRow(query).Scan(&severity)
	if err != nil {
		return severity, fmt.Errorf("getSeverity.QueryRow: %w", err)
	}

	return severity, nil
}

func updateSeverity(tx *sql.Tx, severity string) error {
	const query = `
		update severity set severity = ?
	`

	_, err := tx.Exec(query, severity)
	if err != nil {
		return fmt.Errorf("updateSeverity.Exec: %w", err)
	}

	return nil
}

func postResolveAlert(w http.ResponseWriter, r *http.Request) {
	idParam := chi.URLParam(r, "id")
	id, err := strconv.Atoi(idParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postResolveAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = resolveAlert(tx, id)
	if err != nil {
		log.Printf("postResolveAlert.resolveAlert: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alerts, err := getOngoingAlerts(tx)
	if err != nil {
		log.Printf("postResolveAlert.getOngoingAlerts: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	newSeverity := "blue"
	for _, alert := range alerts {
		if alert.Severity == "amber" {
			newSeverity = "amber"
			continue
		}

		if alert.Severity == "red" {
			newSeverity = "red"
			break
		}
	}

	err = updateSeverity(tx, newSeverity)
	if err != nil {
		log.Printf("postResolveAlert.updateSeverity: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postResolveAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts/"+idParam)
}

func unresolveAlert(tx *sql.Tx, id int) error {
	const query = `
		update alert set ended_at = null where id = ?
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("unresolveAlert.Exec: %w", err)
	}

	return nil
}

func postUnresolveAlert(w http.ResponseWriter, r *http.Request) {
	idParam := chi.URLParam(r, "id")
	id, err := strconv.Atoi(idParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postUnresolveAlert.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = unresolveAlert(tx, id)
	if err != nil {
		log.Printf("postUnresolveAlert.resolveAlert: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	alerts, err := getOngoingAlerts(tx)
	if err != nil {
		log.Printf("postUnresolveAlert.getOngoingAlerts: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	newSeverity := "blue"
	for _, alert := range alerts {
		if alert.Severity == "amber" {
			newSeverity = "amber"
			continue
		}

		if alert.Severity == "red" {
			newSeverity = "red"
			break
		}
	}

	err = updateSeverity(tx, newSeverity)
	if err != nil {
		log.Printf("postUnresolveAlert.updateSeverity: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postUnresolveAlert.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts/"+idParam)
}

func getAddAlertMessage(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getAddAlertMessage.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	alert, err := getAlertByID(tx, id)
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusNotFound)
			return
		}
		log.Printf("getAddAlertMessage.getAlertByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getAddAlertMessage.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}{{.Alert.Title}} - add message{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/alerts/{{.Alert.ID}}" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
						{{if not .Alert.EndedAt }}
							{{if eq .Alert.AlertType "incident"}}
								<div class="live">LIVE</div>
							{{else}}
								<div class="active">ACTIVE</div>
							{{end}}
						{{end}}
						<h2>{{.Alert.Title}}</h2>
					</div>
				</div>

				<form hx-post hx-swap="none">
					<label>
						Message
						<textarea name="message" required></textarea>
					</label>

					<div>
						<button type="submit">Publish</button>
					</div>
				</form>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getAddAlertMessage", markup)
	if err != nil {
		log.Printf("getAddAlertMessage.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Alert AlertDetail
			Ctx   pageCtx
		}{
			Alert: alert,
			Ctx:   getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getAddAlertMessage.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func createAlertMessage(tx *sql.Tx, alertID int, content string) (int, error) {
	const query = `
		insert into
			alert_message(content, created_at, alert_id)
		values(?, ?, ?)
		returning id
	`

	var id int

	err := tx.QueryRow(query, content, time.Now().UTC(), alertID).Scan(&id)
	if err != nil {
		return id, fmt.Errorf("createAlertMessage.Scan: %w", err)
	}

	return id, nil
}

func postAddAlertMessage(w http.ResponseWriter, r *http.Request) {
	idParam := chi.URLParam(r, "id")

	id, err := strconv.Atoi(idParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	message := r.PostFormValue("message")

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postAddAlertMessage.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	alertMessageID, err := createAlertMessage(tx, id, message)
	if err != nil {
		log.Printf("postAddAlertMessage.createAlertMessage: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = createAlertMessageNotifications(tx, time.Now().UTC(), alertMessageID)
	if err != nil {
		log.Printf("postAddAlertMessage.createAlertMessageNotifications: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postAddAlertMessage.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts/"+idParam)
}

func deleteAlertMessageByID(tx *sql.Tx, alertID int, messageID int) error {
	const query = `
		delete from alert_message where alert_id = ? and id = ?
	`

	_, err := tx.Exec(query, alertID, messageID)
	if err != nil {
		return fmt.Errorf("deleteAlertMessageByID.Exec: %w", err)
	}

	return nil
}

func deleteAlertMessage(w http.ResponseWriter, r *http.Request) {
	alertIDParam := chi.URLParam(r, "id")
	alertID, err := strconv.Atoi(alertIDParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	messageID, err := strconv.Atoi(chi.URLParam(r, "messageID"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("deleteAlertMessage.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = deleteAlertMessageByID(tx, alertID, messageID)
	if err != nil {
		log.Printf("deleteAlertMessage.deleteAlertMessageByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("deleteAlertMessage.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts/"+alertIDParam)
}

func getEditAlertMessage(w http.ResponseWriter, r *http.Request) {
	alertID, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	messageID, err := strconv.Atoi(chi.URLParam(r, "messageID"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getEditAlertMessage.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	alert, err := getAlertByID(tx, alertID)
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusNotFound)
			return
		}
		log.Printf("getEditAlertMessage.getAlertByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getEditAlertMessage.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	message := AlertDetailMessage{}
	for _, msg := range alert.Messages {
		if msg.ID == messageID {
			message = msg
			break
		}
	}

	if message.ID == 0 {
		w.WriteHeader(http.StatusNotFound)
		return
	}

	const markup = `
		{{define "title"}}{{.Alert.Title}} - add message{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/alerts/{{.Alert.ID}}" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
						{{if not .Alert.EndedAt }}
							{{if eq .Alert.AlertType "incident"}}
								<div class="live">LIVE</div>
							{{else}}
								<div class="active">ACTIVE</div>
							{{end}}
						{{end}}
						<h2>{{.Alert.Title}}</h2>
					</div>
				</div>

				<form hx-post hx-swap="none">
					<label>
						Message
						<textarea name="message" required>{{.Message.Content}}</textarea>
					</label>

					<div>
						<button type="submit">Republish</button>
					</div>
				</form>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getEditAlertMessage", markup)
	if err != nil {
		log.Printf("getEditAlertMessage.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Alert   AlertDetail
			Message AlertDetailMessage
			Ctx     pageCtx
		}{
			Alert:   alert,
			Message: message,
			Ctx:     getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getEditAlertMessage.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func editAlertMessage(tx *sql.Tx, alertID int, messageID int, content string) error {
	const query = `
		update alert_message 
		set 
			content = ?,
			last_updated_at = ? 
		where 
			alert_id = ? and id = ?
	`

	_, err := tx.Exec(query, content, time.Now().UTC(), alertID, messageID)
	if err != nil {
		return fmt.Errorf("editAlertMessage.Exec: %w", err)
	}

	return nil
}

func postEditAlertMessage(w http.ResponseWriter, r *http.Request) {
	alertIDParam := chi.URLParam(r, "id")

	alertID, err := strconv.Atoi(alertIDParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	messageID, err := strconv.Atoi(chi.URLParam(r, "messageID"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	message := r.PostFormValue("message")
	if message == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postEditAlertMessage.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = editAlertMessage(tx, alertID, messageID, message)
	if err != nil {
		log.Printf("postEditAlertMessage.editAlertMessage: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postEditAlertMessage.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/alerts/"+alertIDParam)
}

type service struct {
	ID         int
	Name       string
	HelperText string
}

func listServices(tx *sql.Tx) ([]service, error) {
	const query = `
		select 
			id, name, helper_text
		from
			service
	`

	services := []service{}

	rows, err := tx.Query(query)
	if err != nil {
		return services, fmt.Errorf("listServices.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		svc := service{}
		err = rows.Scan(
			&svc.ID,
			&svc.Name,
			&svc.HelperText,
		)
		if err != nil {
			return services, fmt.Errorf("listServices.Scan: %w", err)
		}

		services = append(services, svc)
	}

	return services, nil
}

func services(w http.ResponseWriter, r *http.Request) {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("services.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	services, err := listServices(tx)
	if err != nil {
		log.Printf("services.listServices: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("services.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Services{{end}}
		{{define "body"}}
			<div class="admin-nav-header">
				<div>
					<h2>Services</h2>
				</div>

				<div>
					<a href="/admin/services/create" hx-boost="true">
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
							<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
						</svg>
					</a>
				</div>
			</div>

			{{if eq (len .Services) 0}}
				<div class="entity-empty-state">
					<div class="icon">
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
							<path d="M12 4.467c0-.405.262-.75.559-1.027.276-.257.441-.584.441-.94 0-.828-.895-1.5-2-1.5s-2 .672-2 1.5c0 .362.171.694.456.953.29.265.544.6.544.994a.968.968 0 01-1.024.974 39.655 39.655 0 01-3.014-.306.75.75 0 00-.847.847c.14.993.242 1.999.306 3.014A.968.968 0 014.447 10c-.393 0-.729-.253-.994-.544C3.194 9.17 2.862 9 2.5 9 1.672 9 1 9.895 1 11s.672 2 1.5 2c.356 0 .683-.165.94-.441.276-.297.622-.559 1.027-.559a.997.997 0 011.004 1.03 39.747 39.747 0 01-.319 3.734.75.75 0 00.64.842c1.05.146 2.111.252 3.184.318A.97.97 0 0010 16.948c0-.394-.254-.73-.545-.995C9.171 15.693 9 15.362 9 15c0-.828.895-1.5 2-1.5s2 .672 2 1.5c0 .356-.165.683-.441.94-.297.276-.559.622-.559 1.027a.998.998 0 001.03 1.005c1.337-.05 2.659-.162 3.961-.337a.75.75 0 00.644-.644c.175-1.302.288-2.624.337-3.961A.998.998 0 0016.967 12c-.405 0-.75.262-1.027.559-.257.276-.584.441-.94.441-.828 0-1.5-.895-1.5-2s.672-2 1.5-2c.362 0 .694.17.953.455.265.291.601.545.995.545a.97.97 0 00.976-1.024 41.159 41.159 0 00-.318-3.184.75.75 0 00-.842-.64c-1.228.164-2.473.271-3.734.319A.997.997 0 0112 4.467z" />
						</svg>
					</div>
					<span>Add your first service</span>
					<a class="action" href="/admin/services/create" hx-boost="true">Add service</a>
				</div>
			{{else}}
				<div class="services-container">
					{{range $service := .Services}}
						<div>
							<div>
								<span>{{$service.Name}}</span>
								<span>{{$service.HelperText}}</span>
							</div>
							<div class="menu">
								<button class="menu-button">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
										<path d="M3 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM8.5 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM15.5 8.5a1.5 1.5 0 100 3 1.5 1.5 0 000-3z" />
									</svg>
								</button>

								<dialog>
									<a href="/admin/services/{{$service.ID}}/edit" hx-boost="true">Edit</a>
									<button onclick="document.getElementById('dialog-{{$service.ID}}').showModal();">Delete</button>
								</dialog>
							</div>
							<dialog class="modal" id="dialog-{{$service.ID}}">
								<span>Delete {{$service.Name}}</span>
								<form hx-delete="/admin/services/{{$service.ID}}" hx-swap="none">
									<div>
										<button onclick="document.getElementById('dialog-{{$service.ID}}').close(); return false;">Cancel</button>
										<button><span></span>Delete</button>
									</div>
								</form>
							</dialog>
						</div>
					{{end}}
				</div>
			{{end}}
		{{end}}
	`

	tmpl, err := parseTmpl("services", markup)
	if err != nil {
		log.Printf("services.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Services []service
			Ctx      pageCtx
		}{
			Services: services,
			Ctx:      getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("services.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getCreateService(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Create service{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/services" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						 </a>
				  
						<h2>Create service</h2>
					</div>
				</div>

				<form hx-post hx-swap="none">
					<label>
						Name
						<input name="name" required />
					</label>

					<label>
						Helper text
						<input name="helper" />
					</label>

					<div>
						<button type="submit">Create</button>
					</div>
				</form>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getCreateService", markup)
	if err != nil {
		log.Printf("getCreateService.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Ctx pageCtx
		}{
			Ctx: getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getCreateService.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func createService(tx *sql.Tx, name string, helperText string) error {
	const query = `
		insert into service(name, helper_text) values(?, ?)
	`

	_, err := tx.Exec(query, name, helperText)
	if err != nil {
		return fmt.Errorf("createService.Exec: %w", err)
	}

	return nil
}

func postCreateService(w http.ResponseWriter, r *http.Request) {
	name := r.PostFormValue("name")
	helperText := r.PostFormValue("helper")

	if name == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postCreateService.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	_, err = listServices(tx)
	if err != nil {
		log.Printf("postCreateService.listServices: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = createService(tx, name, helperText)
	if err != nil {
		log.Printf("postCreateService.createService: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postCreateService.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/services")
}

func deleteServiceByID(tx *sql.Tx, id int) error {
	const query = `
		delete from service where id = $1
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("deleteServiceByID.Exec: %w", err)
	}

	return nil
}

func deleteService(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("deleteService.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = deleteServiceByID(tx, id)
	if err != nil {
		log.Printf("deleteService.deleteServiceByID: %s", err)
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("deleteService.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/services")
}

func getServiceByID(tx *sql.Tx, id int) (service, error) {
	const query = `
		select id, name, helper_text from service where id = $1
	`

	service := service{}

	err := tx.QueryRow(query, id).Scan(
		&service.ID,
		&service.Name,
		&service.HelperText,
	)
	if err != nil {
		return service, fmt.Errorf("getServiceByID.Scan: %w", err)
	}

	return service, nil
}

func getEditService(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getEditService.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	svc, err := getServiceByID(tx, id)
	if err != nil {
		log.Printf("getEditService.getServiceByID: %s", err)
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getEditService.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Edit service{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/services" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
					
						<h2>Edit service</h2>
					</div>
				</div>

				<form hx-post hx-swap="none" autocomplete="off">
					<label>
						Title
						<input name="name" value="{{.Service.Name}}" required />
					</label>

					<label>
						Helper text
						<input name="helper" value="{{.Service.HelperText}}">
					</label>

					<div>
						<button type="submit">Edit</button>
					</div>
				</form>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getEditService", markup)
	if err != nil {
		log.Printf("getEditService.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Service service
			Ctx     pageCtx
		}{
			Service: svc,
			Ctx:     getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getEditService.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func editService(tx *sql.Tx, id int, name string, helperText string) error {
	const query = `
		update service set name = ?, helper_text = ? where id = ?
	`

	_, err := tx.Exec(query, name, helperText, id)
	if err != nil {
		return fmt.Errorf("editService.Exec: %w", err)
	}

	return nil
}

func postEditService(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	name := r.PostFormValue("name")
	helperText := r.PostFormValue("helper")

	if name == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postEditService.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = editService(tx, id, name, helperText)
	if err != nil {
		log.Printf("postEditService.createService: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postEditService.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/services")
}

func notifications(w http.ResponseWriter, r *http.Request) {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("notifications.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	channels, err := listNotificationChannels(tx, listNotificationsOptions{})
	if err != nil {
		log.Printf("notifications.listNotificationChannels: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	mailGroups, err := listMailGroups(tx)
	if err != nil {
		log.Printf("notifications.listMailGroups: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("notifications.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Notifications{{end}}
		{{define "body"}}
			<div class="admin-nav-header admin-nav-header--notifications">
				<div>
					<h2>Notifications</h2>
				</div>
			</div>

			<div class="notifications-container">
				<div class="notification-channels-header">
					<h2>Channels</h2>

					<div>
						<a href="/admin/notifications/create" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
								<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
							</svg>
						</a>
					</div>
				</div>

				<div style="margin-bottom: 5.0rem;">
					{{if eq (len .Notifications) 0}}
						<div class="entity-empty-state">
							<div class="icon">
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
									<path fill-rule="evenodd" d="M10 2a6 6 0 0 0-6 6c0 1.887-.454 3.665-1.257 5.234a.75.75 0 0 0 .515 1.076 32.91 32.91 0 0 0 3.256.508 3.5 3.5 0 0 0 6.972 0 32.903 32.903 0 0 0 3.256-.508.75.75 0 0 0 .515-1.076A11.448 11.448 0 0 1 16 8a6 6 0 0 0-6-6ZM8.05 14.943a33.54 33.54 0 0 0 3.9 0 2 2 0 0 1-3.9 0Z" clip-rule="evenodd" />
								</svg>
							</div>
							<span>Add your first notification channel</span>
							<a class="action" href="/admin/notifications/create" hx-boost="true">Add channel</a>
						</div>
					{{else}}
						<div class="notifications-list">
							{{range $notification := .Notifications}}
								<div href="/" hx-boost="true">
									<div>
										{{if eq $notification.Type "smtp"}}
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
												<path d="M3 4a2 2 0 00-2 2v1.161l8.441 4.221a1.25 1.25 0 001.118 0L19 7.162V6a2 2 0 00-2-2H3z" />
												<path d="M19 8.839l-7.77 3.885a2.75 2.75 0 01-2.46 0L1 8.839V14a2 2 0 002 2h14a2 2 0 002-2V8.839z" />
											</svg>
										{{else if eq $notification.Type "slack"}}
											<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
												<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
												<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
												<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
												<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
												<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
												<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
												<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
												<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
											</svg>
										{{end}}
										<div>
											{{if eq $notification.Type "smtp"}}
												{{if $notification.Name}}
													<span>{{$notification.Name}}</span>
												{{else}}
													<span>{{$notification.Details.Host}}</span>
												{{end}}
											{{else}}
												<span>{{$notification.Name}}</span>
											{{end}}
											{{if eq $notification.Type "smtp"}}
											<span>{{$notification.Details.Host}}</span>
											{{end}}
										</div>
									</div>
									<div class="menu">
										<button class="menu-button">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
												<path d="M3 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM8.5 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM15.5 8.5a1.5 1.5 0 100 3 1.5 1.5 0 000-3z" />
											</svg>
										</button>

										<dialog>
											<a href="/admin/notifications/{{$notification.ID}}/edit" hx-boost="true">Edit</a>
											<button onclick="document.getElementById('dialog-channel-{{$notification.ID}}').showModal();">Delete</button>
										</dialog>
									</div>
									<dialog class="modal" id="dialog-channel-{{$notification.ID}}">
										<span>Delete {{$notification.Name}}</span>
										<form hx-delete="/admin/notifications/{{$notification.ID}}" hx-swap="none">
											<div>
												<button onclick="document.getElementById('dialog-channel-{{$notification.ID}}').close(); return false;">Cancel</button>
												<button><span></span>Delete</button>
											</div>
										</form>
									</dialog>
								</div>
							{{end}}
						</div>
					{{end}}
				</div>

				<div class="notification-channels-header">
					<h2>Mail groups</h2>
					<div>
						<a href="/admin/notifications/mail-groups/create" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
								<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
							</svg>
						</a>
					</div>
				</div>

				{{if eq (len .MailGroups) 0}}
					<div class="entity-empty-state">
						<div class="icon">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path d="M3 4a2 2 0 0 0-2 2v1.161l8.441 4.221a1.25 1.25 0 0 0 1.118 0L19 7.162V6a2 2 0 0 0-2-2H3Z" />
								<path d="m19 8.839-7.77 3.885a2.75 2.75 0 0 1-2.46 0L1 8.839V14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2V8.839Z" />
							</svg>
						</div>
						<span>Create your first mail group</span>
						<a class="action" href="/admin/notifications/mail-groups/create" hx-boost="true">Add mail group</a>
					</div>
				{{else}}
					<div class="notifications-list">
						{{range $mailGroup := .MailGroups}}
							<div href="/" hx-boost="true">
								<div>
									<div>
										<span>{{$mailGroup.Name}}</span>
										{{if $mailGroup.Description}}
											<span>{{$mailGroup.Description}}</span>
										{{end}}
									</div>
								</div>
								<div class="menu">
									<button class="menu-button">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
											<path d="M3 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM8.5 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM15.5 8.5a1.5 1.5 0 100 3 1.5 1.5 0 000-3z" />
										</svg>
									</button>

									<dialog>
										<a href="/admin/notifications/mail-groups/{{$mailGroup.ID}}/edit" hx-boost="true">Edit</a>
										<button onclick="document.getElementById('dialog-mail-group-{{$mailGroup.ID}}').showModal();">Delete</button>
									</dialog>
								</div>
								<dialog class="modal" id="dialog-mail-group-{{$mailGroup.ID}}">
									<span>Delete {{$mailGroup.Name}}</span>
									<form hx-delete="/admin/notifications/mail-groups/{{$mailGroup.ID}}" hx-swap="none">
										<div>
											<button onclick="document.getElementById('dialog-mail-group-{{$mailGroup.ID}}').close(); return false;">Cancel</button>
											<button><span></span>Delete</button>
										</div>
									</form>
								</dialog>
							</div>
						{{end}}
					</div>
				{{end}}
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("notifications", markup)
	if err != nil {
		log.Printf("notifications.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Notifications []NotificationChannel
			MailGroups    []MailGroup
			Ctx           pageCtx
		}{
			Notifications: channels,
			MailGroups:    mailGroups,
			Ctx:           getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("notifications.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getCreateNotification(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Create notification channel{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/notifications" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						 </a>
				  
						<h2>Create notification channel</h2>
					</div>
				</div>

				<form hx-post hx-swap="none" autocomplete="off">
					<script>
						function onNotificationTypeSelected(input) {
							if (input.value === "smtp") {
								document.querySelector(".smtp-container").classList.add("smtp-container--visible");
								document.querySelector(".smtp-container").disabled = false;

								document.querySelector(".slack-container").classList.remove("slack-container--visible");
								document.querySelector(".slack-container").disabled = true;
							}

							if (input.value === "slack") {
								document.querySelector(".slack-container").classList.add("slack-container--visible");
								document.querySelector(".slack-container").disabled = false;
										
								document.querySelector(".smtp-container").classList.remove("smtp-container--visible");
								document.querySelector(".smtp-container").disabled = true;
							}
						}
					</script>

					<label>
						Type
					</label>
					<div class="notification-type-group">
						<label>
							<input
								type="radio"
								name="type"
								value="smtp"
								onclick="onNotificationTypeSelected(this);"
								autocomplete="off" 
								checked
								required
							/>
							<span>
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
									<path d="M3 4a2 2 0 00-2 2v1.161l8.441 4.221a1.25 1.25 0 001.118 0L19 7.162V6a2 2 0 00-2-2H3z" />
									<path d="M19 8.839l-7.77 3.885a2.75 2.75 0 01-2.46 0L1 8.839V14a2 2 0 002 2h14a2 2 0 002-2V8.839z" />
								</svg>
								SMTP
							</span>
						</label>
						<label>
							<input 
								type="radio"
								name="type"
								value="slack"
								onclick="onNotificationTypeSelected(this);" 
								autocomplete="off" 
								required
							/>
							<span>
								<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
									<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
									<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
									<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
									<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
									<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
									<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
									<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
									<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
								</svg>
								Slack
							</span>
						</label>
					</div>

					<label>
						Display name
						<input name="display-name" required />
					</label>
					
					<fieldset class="smtp-container smtp-container--visible">
						<legend class="hide">SMTP details</legend>
						<label>
							Host
							<input name="host" oninput="onInputHost(this);" required />
						</label>

						<label>
							Port
							<input name="port" type="number" required />
						</label>

						<label>
							Username
							<input name="username" type="password" required />
						</label>

						<label>
							Password
							<input name="password" type="password" required />
						</label>

						<label>
							From
							<input name="from" type="email" required />
						</label>

						<div></div>

						<fieldset id="postmark" class="postmark" style="display: none;" disabled>
							<label>
								Postmark transactional stream
								<input name="pm-transactional" value="outbound" required />
							</label>

							<label>
								Postmark broadcast stream
								<input name="pm-broadcast" value="broadcast" required />
							</label>
						</fieldset>

						<div class="smtp-headers-container">
							<fieldset class="param-box">
								<legend>Headers</legend>
								<div class="entity-empty-state entity-empty-state--secondary">
									<div class="icon">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
											<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
										</svg>
									</div>
									<span>No headers set</span>
									<button
										class="action"
										type="button"
										onclick="addParamOnClick(this);"
									>
										Add header
									</button>
								</div>
								<fieldset class="param-box__inputs" disabled>
									<legend class="hide">Request headers list</legend>
									<div class="param-box__list">
										<div class="param-box__item">
											<input name="header-key" required placeholder="Key" />
											<input name="header-value" required placeholder="Value" />
											<button type="button" onclick="removeParamOnClick(this);">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
													<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
												</svg>
											</button>
										</div>
									</div>
									<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
										<div>
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
												<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
											</svg>
										</div>
										<span>Add header</span>
									</button>
								</fieldset>
							</fieldset>
						</div>
					</fieldset>

					<fieldset class="slack-container" disabled>
						<legend class="hide">Slack info</legend>
						<label>
							Webhook URL
							<input name="webhook-url" type="url" required />

							<button 
								type="button"
								class="help"
								onclick="document.querySelector('.slack-tutorial').classList.toggle('slack-tutorial--visible');"
							>
								How do I get a webhook URL?
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
									<path fill-rule="evenodd" d="M4.22 6.22a.75.75 0 0 1 1.06 0L8 8.94l2.72-2.72a.75.75 0 1 1 1.06 1.06l-3.25 3.25a.75.75 0 0 1-1.06 0L4.22 7.28a.75.75 0 0 1 0-1.06Z" clip-rule="evenodd" />
								</svg>
							</button>
						</label>

						<div class="slack-tutorial">
							<p>You'll need to create a Slack app (if you haven't already) and then add a new webhook to your workspace.</p>

							<a href="https://api.slack.com/apps/new" target="_blank">
								<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
									<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
									<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
									<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
									<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
									<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
									<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
									<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
									<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
								</svg>
								Create new Slack app
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
									<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
									<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
								</svg>
							</a>

							<p>Select the "From scratch" option</p>
							<img 
								src="/static/images/slack-notification-tutorial/1.png"
								style="width: 60%;"
							/>

							<p>Name your app, choose your Slack workspace, and click “Create app”</p>
							<img 
								src="/static/images/slack-notification-tutorial/2.png"
								style="width: 60%;"
							/>


							<p>Activate incoming webhooks in your app and click “Add New Webhook to Workspace”</p>
							<img 
								src="/static/images/slack-notification-tutorial/3.png"
								style="width: 100%;"
							/>


							<p>Select the Slack channel you'd like to receive notifications in</p>
							<img
								src="/static/images/slack-notification-tutorial/4.png"
								style="width: 60%;"
							/>

							<p>Copy and paste your new webhook URL into statusnook</p>
							<img 
								src="/static/images/slack-notification-tutorial/5.png"
								style="width: 100%;"
							/>
						</div>
					</fieldset>

					<div>
						<button type="submit">Create</button>
					</div>
				</form>
			</div>
			<script>
				function onInputHost(e) {
					const postmarkFieldSet = document.querySelector("#postmark");

					if (e.value.toLowerCase() === "smtp.postmarkapp.com") {
						postmarkFieldSet.style.display = "flex";
						postmarkFieldSet.disabled = false;
					} else {
						postmarkFieldSet.style.display = "none";
						postmarkFieldSet.disabled = true;
					}
				}

				function addParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");

					if (paramBoxInputs.disabled) {
						paramBoxInputs.disabled = false;
						root.querySelector(".entity-empty-state").style.display = "none";
						return;
					}

					const items = root.querySelectorAll(".param-box__item")

					const clone = items[0].cloneNode(true);

					const paramBoxList = root.querySelector(".param-box__list")
							
					const insertedClone = paramBoxList.appendChild(
						clone,
					);

					insertedClone.querySelectorAll("input").forEach(v => {
						v.value = "";
					});
				}
				
				function removeParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");
					
					const items = paramBoxInputs.querySelectorAll(".param-box__item");
					if (items.length === 1) {								
						const emptyState = root.querySelector(".entity-empty-state");
						emptyState.style.display = "flex";
						root.querySelector(".param-box__inputs").disabled = true;
						[...root.querySelectorAll("input")].forEach(v => v.value = "");
					} else {
						e.parentElement.remove();
					}
				}
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getCreateNotification", markup)
	if err != nil {
		log.Printf("getCreateNotification.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Ctx pageCtx
		}{
			Ctx: getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getCreateNotification.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

type SMTPNotificationDetails struct {
	Host     string            `json:"host"`
	Port     int               `json:"port"`
	Username string            `json:"username"`
	Password string            `json:"password"`
	From     string            `json:"from"`
	Headers  map[string]string `json:"headers"`
	Misc     map[string]string `json:"misc"`
}

type SlackNotificationDetails struct {
	WebhookURL string `json:"webhookURL"`
}

type NotificationChannel struct {
	ID      int
	Name    string
	Type    string
	Details any
}

type listNotificationsOptions struct {
	Type string
}

func listNotificationChannels(tx *sql.Tx, options listNotificationsOptions) ([]NotificationChannel, error) {
	const baseQuery = `
		select id, name, type, details from notification_channel
	`

	query := baseQuery

	params := []any{}

	if options.Type != "" {
		query += " where type = ?"
		params = append(params, options.Type)
	}

	var channels []NotificationChannel

	rows, err := tx.Query(query, params...)
	if err != nil {
		return channels, fmt.Errorf("listNotificationChannels.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var detailsStr string
		var channel NotificationChannel

		err := rows.Scan(&channel.ID, &channel.Name, &channel.Type, &detailsStr)
		if err != nil {
			return channels, fmt.Errorf("listNotificationChannels.Scan: %w", err)
		}

		if channel.Type == "smtp" {
			var details SMTPNotificationDetails

			err := json.Unmarshal([]byte(detailsStr), &details)
			if err != nil {
				return channels, fmt.Errorf("listNotificationChannels.UnmarshalSMTP: %w", err)
			}

			channel.Details = details
		} else if channel.Type == "slack" {
			var details SlackNotificationDetails

			err := json.Unmarshal([]byte(detailsStr), &details)
			if err != nil {
				return channels, fmt.Errorf("listNotificationChannels.UnmarshalSlack: %w", err)
			}

			channel.Details = details
		}

		channels = append(channels, channel)
	}

	return channels, nil
}

func listNotificationChannelsByMonitorID(tx *sql.Tx, monitorID int) ([]NotificationChannel, error) {
	const query = `
		select notification_channel.id, notification_channel.name, notification_channel.type, 
		notification_channel.details 
		from monitor_notification_channel
		left join notification_channel on 
			notification_channel.id = monitor_notification_channel.notification_channel_id
		where monitor_notification_channel.monitor_id = ?
	`

	var notifications []NotificationChannel

	rows, err := tx.Query(query, monitorID)
	if err != nil {
		return notifications, fmt.Errorf("listNotificationChannelsByMonitorID.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var detailsStr string
		var channel NotificationChannel

		err := rows.Scan(&channel.ID, &channel.Name, &channel.Type, &detailsStr)
		if err != nil {
			return notifications, fmt.Errorf("listNotificationChannelsByMonitorID.Scan: %w", err)
		}

		if channel.Type == "smtp" {
			var details SMTPNotificationDetails

			err := json.Unmarshal([]byte(detailsStr), &details)
			if err != nil {
				return notifications, fmt.Errorf("listNotificationChannelsByMonitorID.UnmarshalSMTP: %w", err)
			}

			channel.Details = details
		} else if channel.Type == "slack" {
			var details SlackNotificationDetails

			err := json.Unmarshal([]byte(detailsStr), &details)
			if err != nil {
				return notifications, fmt.Errorf("listNotificationChannelsByMonitorID.UnmarshalSlack: %w", err)
			}

			channel.Details = details
		}

		notifications = append(notifications, channel)
	}

	return notifications, nil
}

func createNotification(
	tx *sql.Tx,
	name string,
	notificationType string,
	details string,
) error {
	const query = `
		insert into notification_channel(name, type, details) values(?, ?, ?)
	`

	_, err := tx.Exec(query, name, notificationType, details)
	if err != nil {
		return fmt.Errorf("createNotification.Exec: %w", err)
	}

	return nil
}

func postCreateNotification(w http.ResponseWriter, r *http.Request) {
	notificationType := r.PostFormValue("type")
	if notificationType != "smtp" && notificationType != "slack" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	displayName := r.PostFormValue("display-name")
	if displayName == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	if notificationType == "smtp" {
		host := r.PostFormValue("host")
		if host == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		port := r.PostFormValue("port")
		if port == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		portNum, err := strconv.Atoi(port)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		username := r.PostFormValue("username")
		if username == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		password := r.PostFormValue("password")
		if password == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		from := r.PostFormValue("from")
		if password == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		_, err = mail.ParseAddress(from)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		headers := map[string]string{}
		if r.PostFormValue("header-key") != "" && r.PostFormValue("header-value") != "" {
			for i := 0; i < len(r.Form["header-key"]); i++ {
				headers[r.Form["header-key"][i]] = r.Form["header-value"][i]
			}
		}

		misc := map[string]string{}
		if strings.EqualFold(host, "smtp.postmarkapp.com") {
			txStream := r.PostFormValue("pm-transactional")
			bStream := r.PostFormValue("pm-broadcast")

			if txStream == "" || bStream == "" {
				w.WriteHeader(http.StatusBadRequest)
				return
			}

			misc["pm-transactional"] = txStream
			misc["pm-broadcast"] = bStream
		}

		tx, err := rwDB.Begin()
		if err != nil {
			log.Printf("postCreateNotification.BeginSMTP: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
		defer tx.Rollback()

		details := SMTPNotificationDetails{
			Host:     host,
			Port:     portNum,
			Username: username,
			Password: password,
			From:     from,
			Headers:  headers,
			Misc:     misc,
		}

		serializedDetails, err := json.Marshal(details)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		err = createNotification(
			tx,
			displayName,
			notificationType,
			string(serializedDetails),
		)
		if err != nil {
			log.Printf("postCreateNotification.createNotificationSMTP: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		if err = tx.Commit(); err != nil {
			log.Printf("postCreateNotification.CommitSMTP: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
	} else if notificationType == "slack" {
		webhookURL, err := url.ParseRequestURI(r.PostFormValue("webhook-url"))
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
		}

		tx, err := rwDB.Begin()
		if err != nil {
			log.Printf("postCreateNotification.BeginSlack: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
		defer tx.Rollback()

		details := SlackNotificationDetails{
			WebhookURL: webhookURL.String(),
		}

		serializedDetails, err := json.Marshal(details)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		err = createNotification(
			tx,
			displayName,
			notificationType,
			string(serializedDetails),
		)
		if err != nil {
			log.Printf("postCreateNotification.createNotificationSlack: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		if err = tx.Commit(); err != nil {
			log.Printf("postCreateNotification.CommitSlack: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
	}

	w.Header().Add("HX-Location", "/admin/notifications")
}

func getNotificationChannelByID(tx *sql.Tx, id int) (NotificationChannel, error) {
	const query = `
		select id, name, type, details from notification_channel
		where id = ?
	`

	var channel NotificationChannel
	var detailsStr string

	err := tx.QueryRow(query, id).Scan(
		&channel.ID,
		&channel.Name,
		&channel.Type,
		&detailsStr,
	)
	if err != nil {
		return channel, fmt.Errorf("getNotificationChannelByID.QueryRow: %w", err)
	}

	if channel.Type == "smtp" {
		var details SMTPNotificationDetails

		err := json.Unmarshal([]byte(detailsStr), &details)
		if err != nil {
			return channel, fmt.Errorf("getNotificationChannelByID.UnmarshalSMTP: %w", err)
		}

		channel.Details = details
	} else if channel.Type == "slack" {
		var details SlackNotificationDetails

		err := json.Unmarshal([]byte(detailsStr), &details)
		if err != nil {
			return channel, fmt.Errorf("getNotificationChannelByID.UnmarshalSlack: %w", err)
		}

		channel.Details = details
	}

	return channel, nil
}

func getEditNotification(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getEditNotification.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	channel, err := getNotificationChannelByID(tx, id)
	if err != nil {
		log.Printf("getEditNotification.getNotificationChannelByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getEditNotification.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Edit notification channel{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/notifications" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						 </a>
				  
						<h2>Edit notification channel</h2>
					</div>
				</div>

				<form hx-post hx-swap="none" autocomplete="off">
					<label>
						Type
					</label>
					<div class="notification-type-group">
						{{if eq .Notification.Type "smtp"}}
							<label>
								<input type="radio" name="type" value="smtp" required checked />
								<span>
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
										<path d="M3 4a2 2 0 00-2 2v1.161l8.441 4.221a1.25 1.25 0 001.118 0L19 7.162V6a2 2 0 00-2-2H3z" />
										<path d="M19 8.839l-7.77 3.885a2.75 2.75 0 01-2.46 0L1 8.839V14a2 2 0 002 2h14a2 2 0 002-2V8.839z" />
									</svg>
									SMTP
								</span>
							</label>
						{{end}}
						{{if eq .Notification.Type "slack"}}
							<label>
								<input type="radio" name="type" value="slack" required checked />
								<span>
									<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
										<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
										<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
										<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
										<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
										<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
										<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
										<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
										<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
									</svg>
									Slack
								</span>
							</label>
						{{end}}
					</div>

					<label>
						Display name
						<input name="display-name" value="{{.Notification.Name}}" required />
					</label>
					
					{{if eq .Notification.Type "smtp"}}
						<fieldset class="smtp-container smtp-container--visible">
							<label>
								Host
								<input 
									name="host"
									value="{{.Notification.Details.Host}}"
									oninput="onInputHost(this);"
									required
								>
							</label>

							<label>
								Port
								<input name="port" type="number" value="{{.Notification.Details.Port}}" required />
							</label>

							<label>
								Username
								<input name="username" type="password" value="{{.Notification.Details.Username}}" required />
							</label>

							<label>
								Password
								<input name="password" type="password" value="{{.Notification.Details.Password}}" required />
							</label>

							<label>
								From
								<input name="from" type="email" value="{{.Notification.Details.From}}" required />
							</label>

							<div></div>

							<fieldset 
								id="postmark"
								class="postmark"
								{{if not .IsPostmark}}
									style="display: none;"
									disabled
								{{end}}
							>
								<label>
									Postmark transactional stream
									<input 
										name="pm-transactional"
										value="{{index .Notification.Details.Misc "pm-transactional"}}" 
										required
									>
								</label>

								<label>
									Postmark broadcast stream
									<input 
										name="pm-broadcast"
										value="{{index .Notification.Details.Misc "pm-broadcast"}}"
										required
									>
								</label>
							</fieldset>
			
							<div class="smtp-headers-container">
								<fieldset class="param-box">
									<legend>Headers</legend>
									<div 
										class="entity-empty-state entity-empty-state--secondary"
										{{if .Notification.Details.Headers}}style="display: none;"{{end}}
									>
										<div class="icon">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
												<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
											</svg>
										</div>
										<span>No headers set</span>
										<button
											class="action"
											type="button"
											onclick="addParamOnClick(this);"
										>
											Add header
										</button>
									</div>
									<fieldset 
										class="param-box__inputs"
										{{if not .Notification.Details.Headers}}disabled{{end}}
									>
										<legend class="hide">Headers list</legend>
										<div class="param-box__list">
											{{if len .Notification.Details.Headers}}
												{{range $k, $v := .Notification.Details.Headers}}
													<div class="param-box__item">
														<input name="header-key" required placeholder="Key" value="{{$k}}" />
														<input name="header-value" required placeholder="Value" value="{{$v}}" />
														<button type="button" onclick="removeParamOnClick(this);">
															<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
																<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
															</svg>
														</button>
													</div>
												{{end}}
											{{else}}
												<div class="param-box__item">
													<input name="header-key" required placeholder="Key" />
													<input name="header-value" required placeholder="Value" />
													<button type="button" onclick="removeParamOnClick(this);">
														<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
															<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
														</svg>
													</button>
												</div>
											{{end}}
										</div>
										<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
											<div>
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
													<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
												</svg>
											</div>
											<span>Add header</span>
										</button>
									</fieldset>
								</fieldset>
							</div>
						</fieldset>
					{{else if eq .Notification.Type "slack"}}
						<fieldset class="slack-container slack-container--visible">
							<legend class="hide">Slack info</legend>
							<label>
								Webhook URL
								<input 
									name="webhook-url"
									type="url"
									value="{{.Notification.Details.WebhookURL}}"
									required
								/>

								<button 
									type="button"
									class="help"
									onclick="document.querySelector('.slack-tutorial').classList.toggle('slack-tutorial--visible');"
								>
									How do I get a webhook URL?
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
										<path fill-rule="evenodd" d="M4.22 6.22a.75.75 0 0 1 1.06 0L8 8.94l2.72-2.72a.75.75 0 1 1 1.06 1.06l-3.25 3.25a.75.75 0 0 1-1.06 0L4.22 7.28a.75.75 0 0 1 0-1.06Z" clip-rule="evenodd" />
									</svg>
								</button>
							</label>

							<div class="slack-tutorial">
								<p>You'll need to create a Slack app (if you haven't already) and then add a new webhook to your workspace.</p>

								<a href="https://api.slack.com/apps/new" target="_blank">
									<svg viewBox="0 0 124 124" fill="none" xmlns="http://www.w3.org/2000/svg">
										<path d="M26.3996 78.2003C26.3996 85.3003 20.5996 91.1003 13.4996 91.1003C6.39961 91.1003 0.599609 85.3003 0.599609 78.2003C0.599609 71.1003 6.39961 65.3003 13.4996 65.3003H26.3996V78.2003Z" fill="#E01E5A"/>
										<path d="M32.9004 78.2003C32.9004 71.1003 38.7004 65.3003 45.8004 65.3003C52.9004 65.3003 58.7004 71.1003 58.7004 78.2003V110.5C58.7004 117.6 52.9004 123.4 45.8004 123.4C38.7004 123.4 32.9004 117.6 32.9004 110.5V78.2003Z" fill="#E01E5A"/>
										<path d="M45.8004 26.4001C38.7004 26.4001 32.9004 20.6001 32.9004 13.5001C32.9004 6.4001 38.7004 0.600098 45.8004 0.600098C52.9004 0.600098 58.7004 6.4001 58.7004 13.5001V26.4001H45.8004Z" fill="#36C5F0"/>
										<path d="M45.7996 32.8999C52.8996 32.8999 58.6996 38.6999 58.6996 45.7999C58.6996 52.8999 52.8996 58.6999 45.7996 58.6999H13.4996C6.39961 58.6999 0.599609 52.8999 0.599609 45.7999C0.599609 38.6999 6.39961 32.8999 13.4996 32.8999H45.7996Z" fill="#36C5F0"/>
										<path d="M97.5996 45.7999C97.5996 38.6999 103.4 32.8999 110.5 32.8999C117.6 32.8999 123.4 38.6999 123.4 45.7999C123.4 52.8999 117.6 58.6999 110.5 58.6999H97.5996V45.7999Z" fill="#2EB67D"/>
										<path d="M91.0988 45.8001C91.0988 52.9001 85.2988 58.7001 78.1988 58.7001C71.0988 58.7001 65.2988 52.9001 65.2988 45.8001V13.5001C65.2988 6.4001 71.0988 0.600098 78.1988 0.600098C85.2988 0.600098 91.0988 6.4001 91.0988 13.5001V45.8001Z" fill="#2EB67D"/>
										<path d="M78.1988 97.6001C85.2988 97.6001 91.0988 103.4 91.0988 110.5C91.0988 117.6 85.2988 123.4 78.1988 123.4C71.0988 123.4 65.2988 117.6 65.2988 110.5V97.6001H78.1988Z" fill="#ECB22E"/>
										<path d="M78.1988 91.1003C71.0988 91.1003 65.2988 85.3003 65.2988 78.2003C65.2988 71.1003 71.0988 65.3003 78.1988 65.3003H110.499C117.599 65.3003 123.399 71.1003 123.399 78.2003C123.399 85.3003 117.599 91.1003 110.499 91.1003H78.1988Z" fill="#ECB22E"/>
									</svg>
									Create new Slack app
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
										<path d="M6.22 8.72a.75.75 0 0 0 1.06 1.06l5.22-5.22v1.69a.75.75 0 0 0 1.5 0v-3.5a.75.75 0 0 0-.75-.75h-3.5a.75.75 0 0 0 0 1.5h1.69L6.22 8.72Z" />
										<path d="M3.5 6.75c0-.69.56-1.25 1.25-1.25H7A.75.75 0 0 0 7 4H4.75A2.75 2.75 0 0 0 2 6.75v4.5A2.75 2.75 0 0 0 4.75 14h4.5A2.75 2.75 0 0 0 12 11.25V9a.75.75 0 0 0-1.5 0v2.25c0 .69-.56 1.25-1.25 1.25h-4.5c-.69 0-1.25-.56-1.25-1.25v-4.5Z" />
									</svg>
								</a>

								<p>Select the "From scratch" option</p>
								<img 
									src="/static/images/slack-notification-tutorial/1.png"
									style="width: 60%;"
								/>

								<p>Name your app, choose your Slack workspace, and click “Create app”</p>
								<img 
									src="/static/images/slack-notification-tutorial/2.png"
									style="width: 60%;"
								/>


								<p>Activate incoming webhooks in your app and click “Add New Webhook to Workspace”</p>
								<img 
									src="/static/images/slack-notification-tutorial/3.png"
									style="width: 100%;"
								/>


								<p>Select the Slack channel you'd like to receive notifications in</p>
								<img
									src="/static/images/slack-notification-tutorial/4.png"
									style="width: 60%;"
								/>

								<p>Copy and paste your new webhook URL into statusnook</p>
								<img 
									src="/static/images/slack-notification-tutorial/5.png"
									style="width: 100%;"
								/>
							</div>
						</fieldset>
					{{end}}

					<div>
						<button type="submit">Edit</button>
					</div>
				</form>
			</div>
			<script>
				function onInputHost(e) {
					const postmarkFieldSet = document.querySelector("#postmark");

					if (e.value.toLowerCase() === "smtp.postmarkapp.com") {
						postmarkFieldSet.style.display = "flex";
						postmarkFieldSet.disabled = false;
					} else {
						postmarkFieldSet.style.display = "none";
						postmarkFieldSet.disabled = true;
					}
				}

				function addParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");

					if (paramBoxInputs.disabled) {
						paramBoxInputs.disabled = false;
						root.querySelector(".entity-empty-state").style.display = "none";
						return;
					}

					const items = root.querySelectorAll(".param-box__item")

					const clone = items[0].cloneNode(true);

					const paramBoxList = root.querySelector(".param-box__list")
							
					const insertedClone = paramBoxList.appendChild(
						clone,
					);

					insertedClone.querySelectorAll("input").forEach(v => {
						v.value = "";
					});
				}
				
				function removeParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");
					
					const items = paramBoxInputs.querySelectorAll(".param-box__item");
					if (items.length === 1) {								
						const emptyState = root.querySelector(".entity-empty-state");
						emptyState.style.display = "flex";
						root.querySelector(".param-box__inputs").disabled = true;
						[...root.querySelectorAll("input")].forEach(v => v.value = "");
					} else {
						e.parentElement.remove();
					}
				}
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getEditNotification", markup)
	if err != nil {
		log.Printf("getEditNotification.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	isPostmark := false

	smtpDetail, ok := channel.Details.(SMTPNotificationDetails)
	if ok {
		isPostmark = strings.EqualFold(smtpDetail.Host, "smtp.postmarkapp.com")
	}

	err = tmpl.Execute(
		w,
		struct {
			Notification NotificationChannel
			IsPostmark   bool
			Ctx          pageCtx
		}{
			Notification: channel,
			IsPostmark:   isPostmark,
			Ctx:          getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getEditNotification.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func editNotificationChannel(tx *sql.Tx, channel NotificationChannel) error {
	const query = `
		update notification_channel set name = ?, details = ?
		where id = ?
	`

	_, err := tx.Exec(query, channel.Name, channel.Details, channel.ID)
	if err != nil {
		return fmt.Errorf("editNotificationChannel.Exec: %w", err)
	}

	return nil
}

func postEditNotification(w http.ResponseWriter, r *http.Request) {
	idParam := chi.URLParam(r, "id")
	notificationID, err := strconv.Atoi(idParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postEditNotification.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	channel, err := getNotificationChannelByID(tx, notificationID)
	if err != nil {
		log.Printf("postEditNotification.getNotificationChannelByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	displayName := r.PostFormValue("display-name")
	if displayName == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	if channel.Type == "smtp" {
		host := r.PostFormValue("host")
		if host == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		port := r.PostFormValue("port")
		if port == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		portNum, err := strconv.Atoi(port)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		username := r.PostFormValue("username")
		if username == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		password := r.PostFormValue("password")
		if password == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		from := r.PostFormValue("from")
		if password == "" {
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		_, err = mail.ParseAddress(from)
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
			return
		}

		headers := map[string]string{}
		if r.PostFormValue("header-key") != "" && r.PostFormValue("header-value") != "" {
			for i := 0; i < len(r.Form["header-key"]); i++ {
				headers[r.Form["header-key"][i]] = r.Form["header-value"][i]
			}
		}

		misc := map[string]string{}
		if strings.EqualFold(host, "smtp.postmarkapp.com") {
			txStream := r.PostFormValue("pm-transactional")
			bStream := r.PostFormValue("pm-broadcast")

			if txStream == "" || bStream == "" {
				w.WriteHeader(http.StatusBadRequest)
				return
			}

			misc["pm-transactional"] = txStream
			misc["pm-broadcast"] = bStream
		}

		details := SMTPNotificationDetails{
			Host:     host,
			Port:     portNum,
			Username: username,
			Password: password,
			Headers:  headers,
			From:     from,
			Misc:     misc,
		}

		serializedDetails, err := json.Marshal(details)
		if err != nil {
			log.Printf("postEditNotification.MarshalSMTP: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		err = editNotificationChannel(
			tx,
			NotificationChannel{
				ID:      channel.ID,
				Name:    displayName,
				Type:    channel.Type,
				Details: serializedDetails,
			},
		)
		if err != nil {
			log.Printf("postEditNotification.editNotificationChannelSMTP: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
	} else if channel.Type == "slack" {
		webhookURL, err := url.ParseRequestURI(r.PostFormValue("webhook-url"))
		if err != nil {
			w.WriteHeader(http.StatusBadRequest)
		}

		details := SlackNotificationDetails{
			WebhookURL: webhookURL.String(),
		}

		serializedDetails, err := json.Marshal(details)
		if err != nil {
			log.Printf("postEditNotification.MarshalSlack: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		err = editNotificationChannel(
			tx,
			NotificationChannel{
				ID:      channel.ID,
				Name:    displayName,
				Type:    channel.Type,
				Details: serializedDetails,
			},
		)
		if err != nil {
			log.Printf("postEditNotification.editNotificationChannelSlack: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postEditNotification.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/notifications")
}

func deleteNotificationChannelByID(tx *sql.Tx, id int) error {
	const query = `
		delete from notification_channel where id = $1
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("deleteNotificationChannelByID.Exec: %w", err)
	}

	return nil
}

func deleteNotificationChannel(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("deleteNotificationChannel.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = deleteNotificationChannelByID(tx, id)
	if err != nil {
		log.Printf("deleteNotificationChannel.deleteNotificationChannelByID: %s", err)
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("deleteNotificationChannel.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/notifications")
}

func getCreateMailGroup(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Create mail group{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/notifications" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
				
						<h2>Create mail group</h2>
					</div>
				</div>

				<form hx-post hx-swap="none">
					<label>
						Name
						<input name="name" required />
					</label>

					<label>
						Description
						<input name="description" />
					</label>
					
					<fieldset class="param-box">
						<legend>Members</legend>
						<div class="entity-empty-state entity-empty-state--secondary">
							<div class="icon">
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
									<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
								</svg>
							</div>
							<span>No members</span>
							<button
								class="action"
								type="button"
								onclick="addParamOnClick(this);"
							>
								Add member
							</button>
						</div>
						<fieldset class="param-box__inputs" disabled>
							<legend class="hide">Request headers list</legend>
							<div class="param-box__list">
								<div class="param-box__item">
									<input name="members" type="email" required placeholder="Email address" />
									<button type="button" onclick="removeParamOnClick(this);">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
											<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
										</svg>
									</button>
								</div>
							</div>
							<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
								<div>
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
										<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
									</svg>
								</div>
								<span>Add member</span>
							</button>
						</fieldset>
					</fieldset>

					<div>
						<button type="submit">Create</button>
					</div>
				</form>
			</div>
			<script>
				function addParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");

					if (paramBoxInputs.disabled) {
						paramBoxInputs.disabled = false;
						root.querySelector(".entity-empty-state").style.display = "none";
						return;
					}

					const items = root.querySelectorAll(".param-box__item")

					const clone = items[0].cloneNode(true);

					const paramBoxList = root.querySelector(".param-box__list")
							
					const insertedClone = paramBoxList.appendChild(
						clone,
					);

					insertedClone.querySelectorAll("input").forEach(v => {
						v.value = "";
					});
				}
				
				function removeParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");
					
					const items = paramBoxInputs.querySelectorAll(".param-box__item");
					if (items.length === 1) {								
						const emptyState = root.querySelector(".entity-empty-state");
						emptyState.style.display = "flex";
						root.querySelector(".param-box__inputs").disabled = true;
						[...root.querySelectorAll("input")].forEach(v => v.value = "");
					} else {
						e.parentElement.remove();
					}
				}
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getCreateMailGroup", markup)
	if err != nil {
		log.Printf("getCreateMailGroup.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Ctx pageCtx
		}{
			Ctx: getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getCreateMailGroup.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func getEditMailGroup(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getEditMailGroup.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	mailGroup, err := getMailGroupByID(tx, id)
	if err != nil {
		log.Printf("getEditMailGroup.getMailGroupByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	mailGroupMembers, err := listMailGroupMembersByID(tx, id)
	if err != nil {
		log.Printf("getEditMailGroup.listMailGroupMembersByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getEditMailGroup.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Edit mail group{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/notifications" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						</a>
				
						<h2>Edit mail group</h2>
					</div>
				</div>

				<form hx-post hx-swap="none">
					<label>
						Name
						<input name="name" value="{{.MailGroup.Name}}" required />
					</label>

					<label>
						Description
						<input name="description" value="{{.MailGroup.Description}}" />
					</label>
					
					<fieldset class="param-box">
						<legend>Members</legend>
						<div class="entity-empty-state entity-empty-state--secondary"
							{{if .MailGroupMembers}}style="display: none;"{{end}}
						>
							<div class="icon">
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor">
									<path d="M3 4.75a1 1 0 1 0 0-2 1 1 0 0 0 0 2ZM6.25 3a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 7.25a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM6.25 11.5a.75.75 0 0 0 0 1.5h7a.75.75 0 0 0 0-1.5h-7ZM4 12.25a1 1 0 1 1-2 0 1 1 0 0 1 2 0ZM3 9a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" />
								</svg>
							</div>
							<span>No members</span>
							<button
								class="action"
								type="button"
								onclick="addParamOnClick(this);"
							>
								Add member
							</button>
						</div>
						<fieldset class="param-box__inputs" {{if not .MailGroupMembers}}disabled{{end}}>
							<legend class="hide">Request headers list</legend>
							<div class="param-box__list">
								{{if .MailGroupMembers}}
									{{range $member := .MailGroupMembers}}
										<div class="param-box__item">
											<input 
												name="members"
												type="email"
												required
												placeholder="Email address"
												value="{{$member.EmailAddress}}"
											/>
											<button type="button" onclick="removeParamOnClick(this);">
												<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
													<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
												</svg>
											</button>
										</div>
									{{end}}
								{{else}}
									<div class="param-box__item">
										<input name="members" type="email" required placeholder="Email address" />
										<button type="button" onclick="removeParamOnClick(this);">
											<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
												<path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
											</svg>
										</button>
									</div>
								{{end}}
							</div>
							<button class="param-box__add" type="button" onclick="addParamOnClick(this);">
								<div>
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
										<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
									</svg>
								</div>
								<span>Add member</span>
							</button>
						</fieldset>
					</fieldset>

					<div>
						<button type="submit">Create</button>
					</div>
				</form>
			</div>
			<script>
				function addParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");

					if (paramBoxInputs.disabled) {
						paramBoxInputs.disabled = false;
						root.querySelector(".entity-empty-state").style.display = "none";
						return;
					}

					const items = root.querySelectorAll(".param-box__item")

					const clone = items[0].cloneNode(true);

					const paramBoxList = root.querySelector(".param-box__list")
							
					const insertedClone = paramBoxList.appendChild(
						clone,
					);

					insertedClone.querySelectorAll("input").forEach(v => {
						v.value = "";
					});
				}
				
				function removeParamOnClick(e) {
					const root = e.closest(".param-box");

					const paramBoxInputs = root.querySelector(".param-box__inputs");
					
					const items = paramBoxInputs.querySelectorAll(".param-box__item");
					if (items.length === 1) {								
						const emptyState = root.querySelector(".entity-empty-state");
						emptyState.style.display = "flex";
						root.querySelector(".param-box__inputs").disabled = true;
						[...root.querySelectorAll("input")].forEach(v => v.value = "");
					} else {
						e.parentElement.remove();
					}
				}
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getEditMailGroup", markup)
	if err != nil {
		log.Printf("getEditMailGroup.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			MailGroup        MailGroup
			MailGroupMembers []MailGroupMember
			Ctx              pageCtx
		}{
			MailGroup:        mailGroup,
			MailGroupMembers: mailGroupMembers,
			Ctx:              getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getEditMailGroup.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

type MailGroup struct {
	ID          int
	Name        string
	Description string
}

func listMailGroups(tx *sql.Tx) ([]MailGroup, error) {
	const query = `
		select id, name, description from mail_group
	`

	mailGroups := []MailGroup{}

	rows, err := tx.Query(query)
	if err != nil {
		return mailGroups, fmt.Errorf("listMailGroups.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		mailGroup := MailGroup{}
		err = rows.Scan(&mailGroup.ID, &mailGroup.Name, &mailGroup.Description)
		if err != nil {
			return mailGroups, fmt.Errorf("listMailGroups.Scan: %w", err)
		}

		mailGroups = append(mailGroups, mailGroup)
	}

	return mailGroups, nil
}

func updateMonitorMailGroups(tx *sql.Tx, monitorID int, mailGroupIDs []int) error {
	const deleteQuery = `
		delete from mail_group_monitor where monitor_id = ?
	`

	_, err := tx.Exec(deleteQuery, monitorID)
	if err != nil {
		return fmt.Errorf("updateMonitorMailGroups.ExecDelete: %w", err)
	}

	if len(mailGroupIDs) > 0 {
		const baseInsertQuery = `
			insert into mail_group_monitor(mail_group_id, monitor_id) values
		`

		insertQuery := baseInsertQuery

		params := []any{}

		for i, v := range mailGroupIDs {
			insertQuery += "(?, ?)"
			if i < len(mailGroupIDs)-1 {
				insertQuery += ","
			}
			params = append(params, v, monitorID)
		}

		_, err = tx.Exec(insertQuery, params...)
		if err != nil {
			return fmt.Errorf("updateMonitorMailGroups.ExecInsert: %w", err)
		}
	}

	return nil
}

func listMailGroupIDsByMonitorID(tx *sql.Tx, monitorID int) ([]int, error) {
	const query = `
		select mail_group_id from mail_group_monitor 
		where monitor_id = ?
	`

	ids := []int{}

	rows, err := tx.Query(query, monitorID)
	if err != nil {
		return ids, fmt.Errorf("listMailGroupIDsByMonitorID.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var id int
		err = rows.Scan(&id)
		if err != nil {
			return ids, fmt.Errorf("listMailGroupIDsByMonitorID.Scan: %w", err)
		}

		ids = append(ids, id)
	}

	return ids, nil
}

type MailGroupMember struct {
	ID           int
	EmailAddress string
}

func listMailGroupMembersByID(tx *sql.Tx, id int) ([]MailGroupMember, error) {
	const query = `
		select id, email_address from mail_group_member where mail_group_id = ?
	`

	members := []MailGroupMember{}

	rows, err := tx.Query(query, id)
	if err != nil {
		return members, fmt.Errorf("listMailGroupMembersByID.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		member := MailGroupMember{}
		err = rows.Scan(&member.ID, &member.EmailAddress)
		if err != nil {
			return members, fmt.Errorf("listMailGroupMembersByID.Scan: %w", err)
		}

		members = append(members, member)
	}

	return members, nil
}

func listMailGroupMembersEmailsByMonitorID(tx *sql.Tx, id int) ([]string, error) {
	const query = `
		select distinct email_address from mail_group_member
		left join mail_group on mail_group.id = mail_group_member.mail_group_id
		left join mail_group_monitor on mail_group_monitor.mail_group_id = mail_group.id
		where mail_group_monitor.monitor_id = ?
	`

	emails := []string{}

	rows, err := tx.Query(query, id)
	if err != nil {
		return emails, fmt.Errorf("listMailGroupMembersEmailsByMonitorID.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var email string
		err = rows.Scan(&email)
		if err != nil {
			return emails, fmt.Errorf("listMailGroupMembersEmailsByMonitorID.Scan: %w", err)
		}

		emails = append(emails, email)
	}

	return emails, nil
}

func getMailGroupByID(tx *sql.Tx, id int) (MailGroup, error) {
	const query = `
		select id, name, description from mail_group where id = ?
	`

	mailGroup := MailGroup{}

	err := tx.QueryRow(query, id).Scan(&mailGroup.ID, &mailGroup.Name, &mailGroup.Description)
	if err != nil {
		return mailGroup, fmt.Errorf("getMailGroupByID.QueryRow: %w", err)
	}

	return mailGroup, nil
}

func createMailGroup(tx *sql.Tx, name string, description string) (int, error) {
	const query = `
		insert into mail_group(name, description) values(?, ?) returning id
	`

	var id int

	err := tx.QueryRow(query, name, description).Scan(&id)
	if err != nil {
		return id, fmt.Errorf("createMailGroup.QueryRow: %w", err)
	}

	return id, nil
}

func updateMailGroup(tx *sql.Tx, id int, name string, description string) error {
	const query = `
		update mail_group set name = ?, description = ? where id = ?
	`

	_, err := tx.Exec(query, name, description, id)
	if err != nil {
		return fmt.Errorf("updateMailGroup.Exec: %w", err)
	}

	return nil
}

func updateMailGroupMembers(tx *sql.Tx, id int, members []string) error {
	const deleteQuery = `
		delete from mail_group_member where mail_group_id = ?
	`

	_, err := tx.Exec(deleteQuery, id)
	if err != nil {
		return fmt.Errorf("updateMailGroupMembers.ExecDelete: %w", err)
	}

	if len(members) > 0 {
		const baseInsertQuery = `
			insert into mail_group_member(email_address, mail_group_id)
			values
		`

		insertQuery := baseInsertQuery

		for i := range members {
			insertQuery += "(?, ?)"

			if i != len(members)-1 {
				insertQuery += ","
			}
		}

		params := []any{}
		for _, v := range members {
			params = append(params, v, id)
		}

		insertQuery += " on conflict (mail_group_id, email_address) do nothing"

		_, err := tx.Exec(insertQuery, params...)
		if err != nil {
			return fmt.Errorf("updateMailGroupMembers.ExecInsert: %w", err)
		}
	}

	return nil
}

func postCreateMailGroup(w http.ResponseWriter, r *http.Request) {
	name := r.PostFormValue("name")
	if name == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	description := r.PostFormValue("description")

	if r.PostFormValue("members") != "" {
		for _, v := range r.Form["members"] {
			_, err := mail.ParseAddress(v)
			if err != nil {
				w.WriteHeader(http.StatusBadRequest)
				return
			}
		}
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postCreateMailGroup.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	id, err := createMailGroup(tx, name, description)
	if err != nil {
		log.Printf("postCreateMailGroup.createMailGroup: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMailGroupMembers(tx, id, r.Form["members"])
	if err != nil {
		log.Printf("postCreateMailGroup.updateMailGroupMembers: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postCreateMailGroup.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/notifications")
}

func deleteMailGroupByID(tx *sql.Tx, id int) error {
	const query = `
		delete from mail_group where id = ?
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("deleteMailGroupByID.Exec: %w", err)
	}

	return nil
}

func deleteMailGroup(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("deleteMailGroup.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = deleteMailGroupByID(tx, id)
	if err != nil {
		log.Printf("deleteMailGroup.deleteMailGroupByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("deleteMailGroup.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/notifications")
}

func postEditMailGroup(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	name := r.PostFormValue("name")
	if name == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	description := r.PostFormValue("description")

	if r.PostFormValue("members") != "" {
		for _, v := range r.Form["members"] {
			_, err := mail.ParseAddress(v)
			if err != nil {
				w.WriteHeader(http.StatusBadRequest)
				return
			}
		}
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postEditMailGroup.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updateMailGroup(tx, id, name, description)
	if err != nil {
		log.Printf("postEditMailGroup.updateMailGroup: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMailGroupMembers(tx, id, r.Form["members"])
	if err != nil {
		log.Printf("postEditMailGroup.updateMailGroupMembers: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postEditMailGroup.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	w.Header().Add("HX-Location", "/admin/notifications")
}

func update(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Update{{end}}
		{{define "body"}}
			<div class="admin-nav-header">
				<div>
					<h2>Update</h2>
				</div>
			</div>

			<div class="update-container">
				<div>
					<span>Current version</span>
					<span>{{.CurrentVersion}}</span>
				</div>
				<hr>
				<div class="new-update-title" hx-get="/admin/update/check" hx-trigger="load" hx-swap="outerHTML">
					<div>
						<div class="icon icon--rotate">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
								<path fill-rule="evenodd" d="M13.836 2.477a.75.75 0 0 1 .75.75v3.182a.75.75 0 0 1-.75.75h-3.182a.75.75 0 0 1 0-1.5h1.37l-.84-.841a4.5 4.5 0 0 0-7.08.932.75.75 0 0 1-1.3-.75 6 6 0 0 1 9.44-1.242l.842.84V3.227a.75.75 0 0 1 .75-.75Zm-.911 7.5A.75.75 0 0 1 13.199 11a6 6 0 0 1-9.44 1.241l-.84-.84v1.371a.75.75 0 0 1-1.5 0V9.591a.75.75 0 0 1 .75-.75H5.35a.75.75 0 0 1 0 1.5H3.98l.841.841a4.5 4.5 0 0 0 7.08-.932.75.75 0 0 1 1.025-.273Z" clip-rule="evenodd" />
							</svg>									
						</div>
						<span>Checking for updates...</span>
					</div>
				</div>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("update", markup)
	if err != nil {
		log.Printf("update.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			CurrentVersion string
			Ctx            pageCtx
		}{
			CurrentVersion: VERSION,
			Ctx:            getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("update.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func updateCheck(w http.ResponseWriter, r *http.Request) {
	httpClient := http.Client{
		Timeout: time.Second * 10,
	}

	req, err := http.NewRequest(
		http.MethodGet,
		"https://api.github.com/repos/goksan/statusnook/releases/latest", nil,
	)
	if err != nil {
		log.Printf("updateCheck.NewRequest: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	resp, err := httpClient.Do(req)
	if err != nil {
		log.Printf("updateCheck.Do: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		log.Printf("updateCheck.ReadAll: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	type GitHubReleaseAsset struct {
		Name string `json:"name"`
	}

	type GitHubRelease struct {
		TagName     string               `json:"tag_name"`
		Assets      []GitHubReleaseAsset `json:"assets"`
		Body        string               `json:"body"`
		PublishedAt time.Time            `json:"published_at"`
	}

	latestRelease := GitHubRelease{}

	err = json.Unmarshal(body, &latestRelease)
	if err != nil {
		log.Printf("updateCheck.Unmarshal: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	updateAvailable := semver.Compare(latestRelease.TagName, VERSION) > 0
	latestVersion := latestRelease.TagName

	const markup = `
		<div>
			{{if .UpdateAvailable}}
				<div class="new-update-title">
					<div>
						<div class="icon">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
								<path d="M8.75 2.75a.75.75 0 0 0-1.5 0v5.69L5.03 6.22a.75.75 0 0 0-1.06 1.06l3.5 3.5a.75.75 0 0 0 1.06 0l3.5-3.5a.75.75 0 0 0-1.06-1.06L8.75 8.44V2.75Z" />
								<path d="M3.5 9.75a.75.75 0 0 0-1.5 0v1.5A2.75 2.75 0 0 0 4.75 14h6.5A2.75 2.75 0 0 0 14 11.25v-1.5a.75.75 0 0 0-1.5 0v1.5c0 .69-.56 1.25-1.25 1.25h-6.5c-.69 0-1.25-.56-1.25-1.25v-1.5Z" />
							</svg>					  
						</div>
						<span>Updates are available</span>
					</div>
					{{if not .Docker}}
						<button onclick="document.getElementById('update-dialog').showModal();">
							<span>Update</span>
						</button>
					{{end}}
				</div>
				<div class="new-update-details">
					<div>
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
							<path fill-rule="evenodd" d="M4.5 2A2.5 2.5 0 0 0 2 4.5v2.879a2.5 2.5 0 0 0 .732 1.767l4.5 4.5a2.5 2.5 0 0 0 3.536 0l2.878-2.878a2.5 2.5 0 0 0 0-3.536l-4.5-4.5A2.5 2.5 0 0 0 7.38 2H4.5ZM5 6a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" clip-rule="evenodd" />
						</svg>
						<span>{{.LatestVersion}}</span>
					</div>
					<div>
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
							<path d="M5.75 7.5a.75.75 0 1 0 0 1.5.75.75 0 0 0 0-1.5ZM5 10.25a.75.75 0 1 1 1.5 0 .75.75 0 0 1-1.5 0ZM10.25 7.5a.75.75 0 1 0 0 1.5.75.75 0 0 0 0-1.5ZM7.25 8.25a.75.75 0 1 1 1.5 0 .75.75 0 0 1-1.5 0ZM8 9.5A.75.75 0 1 0 8 11a.75.75 0 0 0 0-1.5Z" />
							<path fill-rule="evenodd" d="M4.75 1a.75.75 0 0 0-.75.75V3a2 2 0 0 0-2 2v7a2 2 0 0 0 2 2h8a2 2 0 0 0 2-2V5a2 2 0 0 0-2-2V1.75a.75.75 0 0 0-1.5 0V3h-5V1.75A.75.75 0 0 0 4.75 1ZM3.5 7a1 1 0 0 1 1-1h7a1 1 0 0 1 1 1v4.5a1 1 0 0 1-1 1h-7a1 1 0 0 1-1-1V7Z" clip-rule="evenodd" />
						</svg>
						<span>{{.PublishedAt}}</span>
					</div>
				</div>
			{{else}}
				<div class="new-update-title">
					<div>
						<div class="icon">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
								<path fill-rule="evenodd" d="M12.416 3.376a.75.75 0 0 1 .208 1.04l-5 7.5a.75.75 0 0 1-1.154.114l-3-3a.75.75 0 0 1 1.06-1.06l2.353 2.353 4.493-6.74a.75.75 0 0 1 1.04-.207Z" clip-rule="evenodd" />
							</svg>							  
						</div>
						<span>Statusnook is up to date</span>
					</div>
				</div>
			{{end}}
		</div>
		{{if .UpdateAvailable}}
			<p class="new-update-notes">{{.UpdateBody}}</p>
		{{end}}
		<dialog class="modal" id="update-dialog">
			<span>Update to {{.LatestVersion}}</span>
			<form hx-post hx-swap="outerHTML" hx-target="#update-dialog">
				<div>
					<button onclick="document.getElementById('update-dialog').close(); return false;">Cancel</button>
					<button>Start update</button>
				</div>
			</form>
		</dialog>
	`

	tmpl, err := parseTmpl("updateCheck", markup)
	if err != nil {
		log.Printf("updateCheck.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			UpdateAvailable bool
			LatestVersion   string
			PublishedAt     string
			UpdateBody      string
			Docker          bool
			Ctx             pageCtx
		}{

			UpdateAvailable: updateAvailable,
			LatestVersion:   latestVersion,
			PublishedAt:     latestRelease.PublishedAt.Format("2006/01/02"),
			UpdateBody:      latestRelease.Body,
			Docker:          *dockerFlag,
			Ctx:             getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("updateCheck.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func afterUpdate(w http.ResponseWriter, r *http.Request) {
	const markup = `	
		<div id="update-overlay" hx-swap="none">
			<img src="/static/images/statusnook.svg" width="226" height="59">
			<span>Successfully installed {{.Version}}</span>
			<button onclick="location.reload();"><span>Continue</span></button>
		</div>
	`

	tmpl, err := parseTmpl("afterUpdate", markup)
	if err != nil {
		log.Printf("afterUpdate.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Version string
			Ctx     pageCtx
		}{
			Version: VERSION,
			Ctx:     getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("afterUpdate.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postUpdate(w http.ResponseWriter, r *http.Request) {
	httpClient := http.Client{
		Timeout: time.Second * 10,
	}

	req, err := http.NewRequest(
		http.MethodGet,
		"https://api.github.com/repos/goksan/statusnook/releases/latest",
		nil,
	)
	if err != nil {
		log.Printf("postUpdate.NewRequest: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	resp, err := httpClient.Do(req)
	if err != nil {
		log.Printf("postUpdate.Do: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		log.Printf("postUpdate.ReadAll: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	type GitHubReleaseAsset struct {
		Name string `json:"name"`
		URL  string `json:"url"`
	}

	type GitHubRelease struct {
		TagName string               `json:"tag_name"`
		Assets  []GitHubReleaseAsset `json:"assets"`
	}

	latestRelease := GitHubRelease{}

	err = json.Unmarshal(body, &latestRelease)
	if err != nil {
		log.Printf("postUpdate.Unmarshal: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	updateAvailable := semver.Compare(latestRelease.TagName, VERSION) > 0
	latestVersion := latestRelease.TagName

	if !updateAvailable {
		return
	}

	downloadURL := ""

	for _, asset := range latestRelease.Assets {
		if strings.Contains(asset.Name, runtime.GOOS+"_"+runtime.GOARCH) {
			downloadURL = asset.URL
		}
	}

	if downloadURL == "" {
		log.Printf("postUpdate.downloadURL: no download URL")
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	downloadReq, err := http.NewRequest(http.MethodGet, downloadURL, nil)
	if err != nil {
		log.Printf("postUpdate.NewRequestDownload: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	downloadReq.Header.Add("Accept", "application/octet-stream")

	resp, err = httpClient.Do(downloadReq)
	if err != nil {
		log.Printf("postUpdate.DoDownload: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer resp.Body.Close()

	err = os.Remove("statusnook")
	if err != nil {
		log.Printf("postUpdate.Remove: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	file, err := os.Create("statusnook")
	if err != nil {
		log.Printf("postUpdate.Create: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = file.Chmod(0700)
	if err != nil {
		log.Printf("postUpdate.Chmod: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	_, err = io.Copy(file, resp.Body)
	if err != nil {
		log.Printf("postUpdate.Copy: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	file.Close()

	const markup = `
		<div 
			id="update-overlay"
			hx-get="/admin/update/after-update"
			hx-trigger="every 2s"
			hx-swap="outerHTML"
		>
			{{.Svg}}
			<span class="loader"></span>
		</div>
	`

	tmpl, err := parseTmpl("postUpdate", markup)
	if err != nil {
		log.Printf("postUpdate.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	svg, err := staticFS.ReadFile("static/images/statusnook.svg")
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Ctx             pageCtx
			Svg             template.HTML
			Version         string
			UpdateAvailable bool
			LatestVersion   string
		}{

			Ctx:             getPageCtx(r),
			Svg:             template.HTML(svg),
			UpdateAvailable: updateAvailable,
			LatestVersion:   latestVersion,
		},
	)
	if err != nil {
		log.Printf("postUpdate.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	syscall.Kill(syscall.Getpid(), syscall.SIGINT)
}

func getSettings(w http.ResponseWriter, r *http.Request) {
	refresh := r.URL.Query().Get("refresh") != ""

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getSettings.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	users, err := listUsers(tx)
	if err != nil {
		log.Printf("getSettings.listUsers: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	invitations, err := listActiveUserInvitations(tx, time.Now().UTC().Add(-time.Hour*24))
	if err != nil {
		log.Printf("getSettings.listActiveUserInvitations: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("getSettings.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	type FormattedInvitation struct {
		ID        int
		Token     string
		ExpiresIn string
	}

	formattedInvitations := make([]FormattedInvitation, 0, len(invitations))

	for _, invitation := range invitations {
		expiresIn := invitation.CreatedAt.Add(time.Hour * 24).Sub(time.Now().UTC())
		h := int(expiresIn.Truncate(time.Hour).Hours())
		m := int(expiresIn.Truncate(time.Minute).Minutes()) - (h * 60)
		formattedInvitations = append(
			formattedInvitations,
			FormattedInvitation{
				ID:        invitation.ID,
				Token:     invitation.Token,
				ExpiresIn: fmt.Sprintf("%dh %dm", h, m),
			},
		)
	}

	const markup = `
		{{define "title"}}Settings{{end}}
		{{define "body"}}
			<div class="admin-nav-header">
				<div>
					<h2>Settings</h2>
				</div>
			</div>

			<div class="settings-container">
				<form hx-post="" autocomplete="off" hx-swap="none">
					<div>
						<label for="name">
							Name
						</label>

						<div class="edit-row">
							<input id="name" name="name" value="{{.Ctx.Name}}" disabled>

							<button 
								type="button"
								class="edit-button"
								onclick="document.querySelector('#name').disabled = false;"
							>
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
									<path d="M13.488 2.513a1.75 1.75 0 0 0-2.475 0L6.75 6.774a2.75 2.75 0 0 0-.596.892l-.848 2.047a.75.75 0 0 0 .98.98l2.047-.848a2.75 2.75 0 0 0 .892-.596l4.261-4.262a1.75 1.75 0 0 0 0-2.474Z" />
									<path d="M4.75 3.5c-.69 0-1.25.56-1.25 1.25v6.5c0 .69.56 1.25 1.25 1.25h6.5c.69 0 1.25-.56 1.25-1.25V9A.75.75 0 0 1 14 9v2.25A2.75 2.75 0 0 1 11.25 14h-6.5A2.75 2.75 0 0 1 2 11.25v-6.5A2.75 2.75 0 0 1 4.75 2H7a.75.75 0 0 1 0 1.5H4.75Z" />
								</svg>
							</button>

							<button class="confirm-button">
								Confirm
							</button>

							<button
								type="button"
								class="cancel-button"
								onclick="document.querySelector('#name').disabled = true;"
							>
								Cancel
							</button>
						</div>
					</div>
				</form>

				<form hx-post="" autocomplete="off" hx-swap="none">
					<label for="domain">
						Domain
					</label>

					{{if .Ctx.UnconfirmedDomainProblem}}
						<div id="banner" class="banner">
							<span>{{.Ctx.UnconfirmedDomainProblem}}</span>
						</div>
					{{else}}
						<div id="banner" class="banner"></div>
					{{end}}

					{{if .Ctx.UnconfirmedDomain}}				
						{{if not .Ctx.UnconfirmedDomainProblem}}
							<div class="banner banner--info">
								<span>
									Checking for an A record on "{{.Ctx.UnconfirmedDomain}}" every minute
								</span>
								<a hx-post="/admin/settings/cancel-domain">Cancel</a>
							</div>
						{{end}}
					{{end}}

					{{if and .Ctx.UnconfirmedDomain .Ctx.UnconfirmedDomainProblem}}
						<div class="domain-row">
							<input 
								id="domain"
								name="domain"
								value="{{.Ctx.UnconfirmedDomain}}"
							>

							<button class="confirm-button">
								Confirm
							</button>
						</div>
					{{end}}

					{{if and .Domain (not .Ctx.UnconfirmedDomain)}}
						<div class="edit-row">
							<input id="domain" name="domain" value="{{.Ctx.Domain}}" disabled>

							<button 
								type="button"
								class="edit-button"
								onclick="document.querySelector('#domain').disabled = false;"
							>
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
									<path d="M13.488 2.513a1.75 1.75 0 0 0-2.475 0L6.75 6.774a2.75 2.75 0 0 0-.596.892l-.848 2.047a.75.75 0 0 0 .98.98l2.047-.848a2.75 2.75 0 0 0 .892-.596l4.261-4.262a1.75 1.75 0 0 0 0-2.474Z" />
									<path d="M4.75 3.5c-.69 0-1.25.56-1.25 1.25v6.5c0 .69.56 1.25 1.25 1.25h6.5c.69 0 1.25-.56 1.25-1.25V9A.75.75 0 0 1 14 9v2.25A2.75 2.75 0 0 1 11.25 14h-6.5A2.75 2.75 0 0 1 2 11.25v-6.5A2.75 2.75 0 0 1 4.75 2H7a.75.75 0 0 1 0 1.5H4.75Z" />
								</svg>
							</button>

							<button class="confirm-button">
								Confirm
							</button>

							<button
								type="button"
								class="cancel-button"
								onclick="document.querySelector('#domain').disabled = true;"
							>
								Cancel
							</button>
						</div>
					{{end}}
				</form>

				<div class="settings-users-header">
					<h3>Users</h3>
				</div>
				<div
					id="users-container" 
					class="users-container"
					{{if .Refresh}}hx-swap-oob="true"{{end}}
				>
					{{range $user := .Users}}
						<div>
							<div>
								<span>{{$user.Username}}</span>
							</div>
							<div class="menu">
								<button class="menu-button">
									<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
										<path d="M3 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM8.5 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM15.5 8.5a1.5 1.5 0 100 3 1.5 1.5 0 000-3z" />
									</svg>
								</button>

								<dialog>
									<a href="/admin/settings/users/{{$user.ID}}/edit" hx-boost="true">Edit</a>
									{{if ne $.Ctx.Auth.ID $user.ID }}
										<button onclick="document.getElementById('dialog-{{$user.ID}}').showModal();">Delete</button>
									{{end}}
								</dialog>
							</div>
							<dialog class="modal" id="dialog-{{$user.ID}}">
								<span>Delete {{$user.Username}}</span>
								<form 
									hx-delete="/admin/settings/users/{{$user.ID}}"
									hx-swap="none"
									hx-on::after-request="htmx.ajax('GET', '?refresh=true', {swap: 'none'});"
								>
									<div>
										<button onclick="document.getElementById('dialog-{{$user.ID}}').close(); return false;">Cancel</button>
										<button><span></span>Delete</button>
									</div>
								</form>
							</dialog>
						</div>
					{{end}}

					{{if .Refresh}}
						<script>
							[...document.querySelectorAll("#users-container .menu-button")].forEach(function(e) {
								e.addEventListener("click", function() {
									const options = e.closest(".menu").querySelector("dialog");
									if (!options.open) {
										[...document.querySelectorAll("dialog:not(.modal)")].forEach(e => {e.close();});
										options.show();
										document.addEventListener("click", onClick);
									} else {
										options.close();
									}
								});
							});
						</script>
					{{end}}
				</div>

				<div class="settings-users-header">
					<h3>Invitations</h3>

					<a
						hx-post="/admin/settings/users/invite"
						hx-swap="none"
						hx-on::after-request="htmx.ajax('GET', '?refresh=true', {swap: 'none'});"
					>
						<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
							<path d="M10.75 4.75a.75.75 0 00-1.5 0v4.5h-4.5a.75.75 0 000 1.5h4.5v4.5a.75.75 0 001.5 0v-4.5h4.5a.75.75 0 000-1.5h-4.5v-4.5z" />
						</svg>
					</a>
				</div>
				<div 
					id="invites-container"
					class="users-container"
					{{if .Refresh}}hx-swap-oob="true"{{end}}
				>
					{{if len .Invitations}}
						{{range $invite := .Invitations}}
							<div>
								<div>
									<span>https://{{$.Ctx.Domain}}/invitation/{{$invite.Token}}</span>
									<span>Expires in {{$invite.ExpiresIn}}</span>
								</div>
								<div class="menu">
									<button class="menu-button">
										<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor" class="w-5 h-5">
											<path d="M3 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM8.5 10a1.5 1.5 0 113 0 1.5 1.5 0 01-3 0zM15.5 8.5a1.5 1.5 0 100 3 1.5 1.5 0 000-3z" />
										</svg>
									</button>

									<dialog>
										<button 
											href="/admin/settings/users/{{$invite.ID}}/edit"
											onclick="navigator.clipboard.writeText('https://{{$.Ctx.Domain}}/invitation/{{$invite.Token}}');"
										>
											Copy
										</button>
										<button onclick="document.getElementById('invitation-dialog-{{$invite.ID}}').showModal();">Delete</button>
									</dialog>
								</div>
								<dialog class="modal" id="invitation-dialog-{{$invite.ID}}">
									<span>Delete invite</span>
									<form 
										hx-delete="/admin/settings/users/invite/{{$invite.ID}}"
										hx-swap="none"
										hx-on::after-request="htmx.ajax('GET', '?refresh=true', {swap: 'none'});"
									>
										<div>
											<button onclick="document.getElementById('invitation-dialog-{{$invite.ID}}').close(); return false;">Cancel</button>
											<button><span></span>Delete</button>
										</div>
									</form>
								</dialog>
							</div>
						{{end}}
					{{else}}
						<div class="entity-empty-state">
							<div class="icon">
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
									<path d="M8 8a2.5 2.5 0 1 0 0-5 2.5 2.5 0 0 0 0 5ZM3.156 11.763c.16-.629.44-1.21.813-1.72a2.5 2.5 0 0 0-2.725 1.377c-.136.287.102.58.418.58h1.449c.01-.077.025-.156.045-.237ZM12.847 11.763c.02.08.036.16.046.237h1.446c.316 0 .554-.293.417-.579a2.5 2.5 0 0 0-2.722-1.378c.374.51.653 1.09.813 1.72ZM14 7.5a1.5 1.5 0 1 1-3 0 1.5 1.5 0 0 1 3 0ZM3.5 9a1.5 1.5 0 1 0 0-3 1.5 1.5 0 0 0 0 3ZM5 13c-.552 0-1.013-.455-.876-.99a4.002 4.002 0 0 1 7.753 0c.136.535-.324.99-.877.99H5Z" />
								</svg>
							</div>
							<span>Invite another admin</span>
							<a 
								class="action"
								hx-post="/admin/settings/users/invite"
								hx-swap="none"
								hx-on::after-request="htmx.ajax('GET', '?refresh=true', {swap: 'none'});"
							>
								Create invite
							</a>
						</div>
					{{end}}
					{{if .Refresh}}
						<script>
							[...document.querySelectorAll("#invites-container .menu-button")].forEach(function(e) {
								e.addEventListener("click", function() {
									const options = e.closest(".menu").querySelector("dialog");
									if (!options.open) {
										[...document.querySelectorAll("dialog:not(.modal)")].forEach(e => {e.close();});
										options.show();
										document.addEventListener("click", onClick);
									} else {
										options.close();
									}
								});
							});
						</script>
					{{end}}
				</div>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getSettings", markup)
	if err != nil {
		log.Printf("getSettings.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			CurrentVersion string
			Domain         string
			Users          []SettingsUser
			Invitations    []FormattedInvitation
			Refresh        bool
			Ctx            pageCtx
		}{
			CurrentVersion: VERSION,
			Domain:         metaDomain,
			Users:          users,
			Invitations:    formattedInvitations,
			Refresh:        refresh,
			Ctx:            getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getSettings.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postSettings(w http.ResponseWriter, r *http.Request) {
	name := r.PostFormValue("name")
	domain := r.PostFormValue("domain")

	if name != "" {
		tx, err := rwDB.Begin()
		if err != nil {
			log.Printf("postSettings.BeginName: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
		defer tx.Rollback()

		err = updateMetaValue(tx, "name", name)
		if err != nil {
			log.Printf("postSettings.updateMetaValueName: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		if err := tx.Commit(); err != nil {
			log.Printf("postSettings.CommitName: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		metaName = name

		escapedName := html.EscapeString(metaName)

		w.Write([]byte(
			fmt.Sprintf(`
				<input id="name" name="name" value="%s" hx-swap-oob="true" disabled>
				<a id="nook-name" href="/" hx-boost="true" hx-swap-oob="true">%s</a>
			`,
				escapedName,
				escapedName,
			),
		))

		return
	}

	if domain != "" {
		if metaSSL != "true" {
			tx, err := rwDB.Begin()
			if err != nil {
				log.Printf("postSettings.BeginUnmanagedDomain: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				w.Write([]byte(
					`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
				))
				return
			}
			defer tx.Rollback()

			err = updateMetaValue(tx, "domain", domain)
			if err != nil {
				log.Printf("postSettings.updateMetaValueDomainUnmanaged: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				w.Write([]byte(
					`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
				))
				return
			}

			err = tx.Commit()
			if err != nil {
				log.Printf("postSettings.CommitUnmanagedDomain: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				w.Write([]byte(
					`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
				))
				return
			}

			metaDomain = domain

			w.Header().Add("HX-Location", "/admin/settings")
			return
		}

		if metaDomain == "" {
			tx, err := rwDB.Begin()
			if err != nil {
				log.Printf("postSettings.BeginUnconfirmedDomainUpdate: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				w.Write([]byte(
					`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
				))
				return
			}
			defer tx.Rollback()

			err = updateMetaValue(tx, "unconfirmedDomain", domain)
			if err != nil {
				log.Printf("postSettings.updateMetaValueUnconfirmedDomainUpdate: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				w.Write([]byte(
					`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
				))
				return
			}

			if err := tx.Commit(); err != nil {
				log.Printf("postSettings.CommitUnconfirmedDomainUpdate: %s", err)
				w.WriteHeader(http.StatusInternalServerError)
				w.Write([]byte(
					`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
				))
				return
			}

			metaUnconfirmedDomain = domain
		}

		found, err := lookupDomain(domain)
		if err != nil {
			log.Printf("postSettings.lookupDomain: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(
				`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
			))
			return
		}

		if !found {
			notFoundMsg := "We didn't find your domain's A record, verify it exists and then retry. " +
				"If your domain and A record is correct, you might need to wait a few minutes before retrying."

			if metaDomain == "" {
				tx, err := rwDB.Begin()
				if err != nil {
					log.Printf("postSettings.BeginUnconfirmedDomainProblemNotFound: %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					w.Write([]byte(
						`
						<div id="banner" class="banner" hx-swap-oob="true">
							<span>An unexpected error occurred</span>
						</div>
					`,
					))
					return
				}
				defer tx.Rollback()

				err = updateMetaValue(tx, "unconfirmedDomainProblem", notFoundMsg)
				if err != nil {
					log.Printf("postSettings.updateMetaValueDomainProblemNotFound: %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					w.Write([]byte(
						`
						<div id="banner" class="banner" hx-swap-oob="true">
							<span>An unexpected error occurred</span>
						</div>
					`,
					))
					return
				}

				if err := tx.Commit(); err != nil {
					log.Printf("postSettings.CommitUnconfirmedDomainProblemNotFound: %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					w.Write([]byte(
						`
						<div id="banner" class="banner" hx-swap-oob="true">
							span>An unexpected error occurred</span>
						</div>
					`,
					))
					return
				}

				metaUnconfirmedDomainProblem = notFoundMsg
			}

			w.WriteHeader(http.StatusBadRequest)
			w.Write([]byte(
				fmt.Sprintf(`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>%s</span>
					</div>
				`,
					notFoundMsg,
				),
			))
			return
		}

		err = attemptCertificateAcquisition(r.Context(), domain)
		if err != nil {
			errMsg := "An unexpected error occurred"

			var acmeProblem acme.Problem
			if errors.As(err, &acmeProblem) {
				var ok bool
				errMsg, ok = acmeProblemTypeMessages[acmeProblem.Type]
				if !ok {
					errMsg = "An unhandled error occurred " +
						acmeProblem.Type
				}
			} else {
				log.Printf("postSettings.attemptCertificateAcquisition: %s", err)
			}

			if metaDomain == "" {
				tx, err := rwDB.Begin()
				if err != nil {
					log.Printf("postSettings.BeginUnconfirmedDomainProblem: %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					w.Write([]byte(
						`
						<div id="banner" class="banner" hx-swap-oob="true">
							<span>An unexpected error occurred</span>
						</div>
					`,
					))
					return
				}
				defer tx.Rollback()

				err = updateMetaValue(tx, "unconfirmedDomainProblem", errMsg)
				if err != nil {
					log.Printf("postSettings.updateMetaValueDomainProblem: %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					w.Write([]byte(
						`
						<div id="banner" class="banner" hx-swap-oob="true">
							<span>An unhandled error occurred</span>
						</div>
					`,
					))
					return
				}

				if err := tx.Commit(); err != nil {
					log.Printf("postSettings.CommitUnconfirmedDomainProblem %s", err)
					w.WriteHeader(http.StatusInternalServerError)
					w.Write([]byte(
						`
						<div id="banner" class="banner" hx-swap-oob="true">
							<span>An unhandled error occurred</span>
						</div>
					`,
					))
					return
				}

				metaUnconfirmedDomainProblem = errMsg
			}

			if errMsg == "An unexpected error occurred" {
				w.WriteHeader(http.StatusInternalServerError)
			} else {
				w.WriteHeader(http.StatusBadRequest)
			}

			w.Write([]byte(
				fmt.Sprintf(`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>%s</span>
					</div>
				`,
					errMsg,
				),
			))
			return
		}

		tx, err := rwDB.Begin()
		if err != nil {
			log.Printf("postSettings.BeginDomain: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(
				`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
			))
			return
		}
		defer tx.Rollback()

		err = updateMetaValue(tx, "domain", domain)
		if err != nil {
			log.Printf("postSettings.updateMetaValueDomain: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(
				`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
			))
			return
		}

		err = updateMetaValue(tx, "unconfirmedDomain", "")
		if err != nil {
			log.Printf("postSettings.updateMetaValueUnconfirmedDomain: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(
				`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
			))
			return
		}

		err = updateMetaValue(tx, "unconfirmedDomainProblem", "")
		if err != nil {
			log.Printf("postSettings.updateMetaValueUnconfirmedDomainProblem: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(
				`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unexpected error occurred</span>
					</div>
				`,
			))
			return
		}

		if err := tx.Commit(); err != nil {
			log.Printf("postSettings.CommitDomain: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(
				`
					<div id="banner" class="banner" hx-swap-oob="true">
						<span>An unhandled error occurred</span>
					</div>
				`,
			))
			return
		}

		metaDomain = domain
		metaUnconfirmedDomain = ""
		metaUnconfirmedDomainProblem = ""

		w.Header().Add("HX-Location", "/admin/settings")
	}
}

func postSettingsCancelDomain(w http.ResponseWriter, r *http.Request) {
	v := "You cancelled the domain verification process. Please enter a new domain."

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postSettingsCancelDomain.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updateMetaValue(tx, "unconfirmedDomainProblem", v)
	if err != nil {
		log.Printf("postSettingsCancelDomain.updateMetaValueProblem: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postSettingsCancelDomain.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	metaUnconfirmedDomainProblem = v

	w.Header().Add("HX-Location", "/admin/settings")
}

func getEditUser(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := db.Begin()
	if err != nil {
		log.Printf("getEditUser.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	username, err := getUsernameByID(tx, id)
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusNotFound)
			return
		}
		log.Printf("getEditUser.getUsernameByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	const markup = `
		{{define "title"}}Edit user{{end}}
		{{define "body"}}
			<div class="create-service-container">
				<div class="admin-nav-header">
					<div>
						<a href="/admin/settings" hx-boost="true">
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M11.78 5.22a.75.75 0 0 1 0 1.06L8.06 10l3.72 3.72a.75.75 0 1 1-1.06 1.06l-4.25-4.25a.75.75 0 0 1 0-1.06l4.25-4.25a.75.75 0 0 1 1.06 0Z" clip-rule="evenodd" />
							</svg>
						 </a>
				  
						<h2>Edit user</h2>
					</div>
				</div>

				<form onsubmit="clearAlerts(this);" hx-post hx-swap="none" autocomplete="off">
					<div id="username-alert"></div>
					<label>
						Username
						<input name="username" value="{{.Username}}" required>
					</label>

					<div id="password-alert"></div>
					<label>
						Password
						<input name="password" type="password" value="retain" required>
					</label>

					<div>
						<button type="submit">Edit</button>
					</div>
				</form>
				<script>
					function clearAlerts(e) {
						[...e.querySelectorAll(".alert")].forEach(v => {
							v.style.display = "none";
						});
					}
				</script>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getEditUser", markup)
	if err != nil {
		log.Printf("getEditUser.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(
		w,
		struct {
			Username string
			Ctx      pageCtx
		}{
			Username: username,
			Ctx:      getPageCtx(r),
		},
	)
	if err != nil {
		log.Printf("getEditUser.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postEditUser(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	username := r.PostFormValue("username")
	if username == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	password := r.PostFormValue("password")
	if password == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	if password != "retain" && len(password) < 8 {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="password-alert" class="alert alert--field" hx-swap-oob="true">
				Password must contain at least 8 characters
			</div>
		`))
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postEditUser.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	_, err = getUsernameByID(tx, id)
	if err != nil {
		if errors.Is(err, sql.ErrNoRows) {
			w.WriteHeader(http.StatusNotFound)
			return
		}
		log.Printf("postEditUser.getUsernameByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if password != "retain" {
		pwHash, err := bcrypt.GenerateFromPassword([]byte(password), bcrypt.DefaultCost)
		if err != nil {
			log.Printf("postEditUser.GenerateFromPassword: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		err = editUser(tx, id, username, string(pwHash))
		if err != nil {
			var sqliteErr sqlite3.Error
			if errors.As(err, &sqliteErr) {
				if errors.Is(sqliteErr.Code, sqlite3.ErrConstraint) {
					w.WriteHeader(http.StatusBadRequest)
					w.Write([]byte(`
						<div id="username-alert" class="alert alert--field" hx-swap-oob="true">
							This username is already taken
						</div>
					`))
					return
				}
			}
			log.Printf("postEditUser.editUser: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		err = deleteAllSessionsByUserID(tx, id)
		if err != nil {
			log.Printf("postEditUser.deleteAllSessionsByUserID: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
	} else {
		err = editUserUsername(tx, id, username)
		if err != nil {
			var sqliteErr sqlite3.Error
			if errors.As(err, &sqliteErr) {
				if errors.Is(sqliteErr.Code, sqlite3.ErrConstraint) {
					w.WriteHeader(http.StatusBadRequest)
					w.Write([]byte(`
						<div id="username-alert" class="alert alert--field" hx-swap-oob="true">
							This username is already taken
						</div>
					`))
					return
				}
			}
			log.Printf("postEditUser.editUserUsername: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postEditUser.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	authCtx := getAuthCtx(r)

	if authCtx.ID == id && password != "retain" {
		w.Header().Add("HX-Location", "/login")
	} else {
		w.Header().Add("HX-Location", "/admin/settings")
	}
}

func deleteUser(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	authCtx := getAuthCtx(r)
	if authCtx.ID == id {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("deleteUser.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = deleteUserByID(tx, id)
	if err != nil {
		log.Printf("deleteUser.deleteUserByID: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("deleteUser.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

type UserInvitation struct {
	ID        int
	Token     string
	CreatedAt time.Time
}

func listActiveUserInvitations(tx *sql.Tx, minTime time.Time) ([]UserInvitation, error) {
	const query = `
		select id, token, created_at from user_invitation
		where created_at > ?
		order by id desc
	`

	invs := []UserInvitation{}

	rows, err := tx.Query(query, minTime)
	if err != nil {
		return invs, fmt.Errorf("listActiveUserInvitations.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var inv UserInvitation
		err := rows.Scan(&inv.ID, &inv.Token, &inv.CreatedAt)
		if err != nil {
			return invs, fmt.Errorf("listActiveUserInvitations.Scan: %w", err)
		}

		invs = append(invs, inv)
	}

	return invs, nil
}

func validateUserInvitationToken(tx *sql.Tx, token string, minTime time.Time) (int, error) {
	const query = `
		select id from user_invitation where token = ? and created_at > ?
	`

	var id int
	err := tx.QueryRow(query, token, minTime).Scan(&id)
	if err != nil {
		return id, fmt.Errorf("validateUserInvitationToken.Scan: %w", err)
	}

	return id, nil
}

func createUserInvitation(tx *sql.Tx, token string, createdAt time.Time) error {
	const query = `
		insert into user_invitation(token, created_at) values(?, ?)
	`

	_, err := tx.Exec(query, token, createdAt)
	if err != nil {
		return fmt.Errorf("createUserInvitation.Exec: %w", err)
	}

	return nil
}

func deleteUserInvitation(tx *sql.Tx, id int) error {
	const query = `
		delete from user_invitation where id = ?
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("deleteUserInvitation.Exec: %w", err)
	}

	return nil
}

func postInviteUser(w http.ResponseWriter, r *http.Request) {
	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postInviteUser.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	tokenBytes := make([]byte, 32)
	_, err = rand.Read(tokenBytes)
	if err != nil {
		log.Printf("postInviteUser.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	token := base64.URLEncoding.EncodeToString(tokenBytes)

	err = createUserInvitation(tx, token, time.Now().UTC())
	if err != nil {
		log.Printf("postInviteUser.createUserInvitation: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postInviteUser.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postDeleteInvite(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(chi.URLParam(r, "id"))
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postDeleteInvite.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = deleteUserInvitation(tx, id)
	if err != nil {
		log.Printf("postDeleteInvite.deleteUserInvitation: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tx.Commit()
	if err != nil {
		log.Printf("postDeleteInvite.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func createSession(tx *sql.Tx, token string, csrfToken string, userID int) error {
	const query = `
		insert into session(token, csrf_token, user_id) values(?, ?, ?)
	`

	_, err := tx.Exec(query, token, csrfToken, userID)
	if err != nil {
		return fmt.Errorf("createSession.Exec: %w", err)
	}

	return nil
}

func validateSession(tx *sql.Tx, token string) (int, string, error) {
	const query = `
		select user.id, session.csrf_Token
		from user
		left join session on session.user_id = user.id
		where session.token = ?
	`

	userID := 0
	csrfToken := ""
	err := tx.QueryRow(query, token).Scan(&userID, &csrfToken)
	if err != nil {
		return userID, csrfToken, err
	}

	return userID, csrfToken, nil
}

type SettingsUser struct {
	ID       int
	Username string
}

func listUsers(tx *sql.Tx) ([]SettingsUser, error) {
	const query = `
		select id, username from user
	`

	users := []SettingsUser{}

	rows, err := tx.Query(query)
	if err != nil {
		return users, fmt.Errorf("listUsers.Query: %w", err)
	}
	defer rows.Close()

	for rows.Next() {
		var user SettingsUser
		err := rows.Scan(&user.ID, &user.Username)
		if err != nil {
			return users, fmt.Errorf("listUsers.Scan: %w", err)
		}

		users = append(users, user)
	}

	return users, nil
}

func getPasswordHash(tx *sql.Tx, username string) (string, int, error) {
	const query = `
		select password, id
		from user
		where username = ?
	`

	hash := ""
	userID := 0
	err := tx.QueryRow(query, username).Scan(&hash, &userID)
	if err != nil {
		return hash, userID, fmt.Errorf("getPasswordHash.QueryRow: %w", err)
	}

	return hash, userID, nil
}

func getUsernameByID(tx *sql.Tx, id int) (string, error) {
	const query = `
		select username from user where id = ?
	`

	username := ""
	err := tx.QueryRow(query, id).Scan(&username)
	if err != nil {
		return username, fmt.Errorf("getUsernameByID.Scan: %w", err)
	}

	return username, nil
}

func deleteSession(tx *sql.Tx, token string) error {
	const query = `
		delete from session where token = ?
	`

	if _, err := tx.Exec(query, token); err != nil {
		return fmt.Errorf("deleteSession.Exec: %w", err)
	}

	return nil
}

func deleteAllSessionsByUserID(tx *sql.Tx, id int) error {
	const query = `
		delete from session where user_id = ?
	`

	if _, err := tx.Exec(query, id); err != nil {
		return fmt.Errorf("deleteAllSessionsByUserID.Exec: %w", err)
	}

	return nil
}

func postSetupStatusnook(w http.ResponseWriter, r *http.Request) {
	w.Header().Add("X-Statusnook-Setup", "true")
	w.Header().Add("Access-Control-Allow-Origin", "*")
	w.Header().Add("Access-Control-Expose-Headers", "X-Statusnook-Setup")
}

func getSetupDomain(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Domain - Statusnook Setup{{end}}
		{{define "body"}}
			<div class="auth-dialog-container">
				{{if eq .SSL "true"}}
					<div class="auth-dialog">
						<div>
							<div>
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
									<path fill-rule="evenodd" d="M10 1a4.5 4.5 0 0 0-4.5 4.5V9H5a2 2 0 0 0-2 2v6a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2v-6a2 2 0 0 0-2-2h-.5V5.5A4.5 4.5 0 0 0 10 1Zm3 8V5.5a3 3 0 1 0-6 0V9h6Z" clip-rule="evenodd" />
								</svg>		
							</div>
							<h1>Domain configuration</h1>
						</div>

						<div class="setup-domain-description">
							<p>Enter a domain that has an A record which is set to this machine's IP address</p>
							<p>A certificate will be obtained via Let's Encrypt and automatically configured</p>
						</div>

						<form onsubmit="onDomainSubmit();" class="setup-domain" hx-post hx-swap="none">
							<div class="domain-alerts">
								<div id="alert"  class="alert domain-alert"></div>
								<div class="alert alert--info domain-alert"></div>
							</div>
							<label>
								Domain
								<input
									oninput="onDomainChange(this);"
									name="domain"
									placeholder="status.example.com"
									{{if .PrefillURLText}}value="{{.PrefillURLText}}"{{end}}
									required
								>
							</label>

							<button>Confirm</button>
							<a class="auth-dialog-continue" href="/setup/account" hx-boost="true">Continue</a>
							<span class="loader"></span>
						</form>

						<div id="skip-domain-setup" class="skip-domain-setup" hx-swap-oob="true">
					</div>
				{{else}}
					<div class="auth-dialog">
						<div>
							<div>
								<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16" fill="currentColor" class="w-4 h-4">
									<path fill-rule="evenodd" d="M4.5 2A2.5 2.5 0 0 0 2 4.5v2.879a2.5 2.5 0 0 0 .732 1.767l4.5 4.5a2.5 2.5 0 0 0 3.536 0l2.878-2.878a2.5 2.5 0 0 0 0-3.536l-4.5-4.5A2.5 2.5 0 0 0 7.38 2H4.5ZM5 6a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" clip-rule="evenodd" />
								</svg>
							</div>
							<h1>Domain configuration</h1>
						</div>

						<div style="margin-bottom: 6.0rem;">
							<p>
								Enter the domain that users will use to visit your Statusnook
							</p>
							<p>
								This domain appears in places such as email links
							</p>
						</div>

						<form class="setup-domain" hx-post hx-swap="none">
							<div id="alert" class="alert"></div>
							<label>
								Domain
								<input
									name="domain"
									placeholder="status.example.com"
									{{if .PrefillURLText}}value="{{.PrefillURLText}}"{{end}}
									required
								>
							</label>

							<button>Confirm</button>
							<span class="loader"></span>
						</form>
					</div>
				{{end}}
			</div>

			<script>
				function onDomainSubmit() {
					const skipDomainSetupEl = document.querySelector(".skip-domain-setup");
					if (skipDomainSetupEl) {
						skipDomainSetupEl.innerHTML = "";
					}
				}

				function onDomainChange() {
					const skipDomainSetupEl = document.querySelector(".skip-domain-setup");
					if (skipDomainSetupEl) {
						skipDomainSetupEl.innerHTML = "";
					}
				}

				async function browserReachabilityTest() {
					const alert = document.querySelector("#alert");
					const alert2 = document.querySelector(".alert:nth-of-type(2)");
					const form = document.querySelector("form");

					alert.innerHTML = "";
					alert2.innerHTML = "";

					form.classList.add("htmx-request");

					
					const successMsg = "<span>We've successfully obtained and configured your certificate!</span>";
					const infoMsg = "<span>However, we've detected your browser can't resolve the domain just yet.</span>" +
						"<span>You may continue to use Statusnook via the instances IP address, we'll redirect you to the domain once we detect your browser can successfully resolve it.</span>";

					try {
						if (form.elements.domain.value.startsWith("https://")) {
							form.elements.domain.value = form.elements.domain.value.replace(
								"https://", 
								"",
							);
						}

						if (form.elements.domain.value.startsWith("http://")) {
							form.elements.domain.value = form.elements.domain.value.replace(
								"http://", 
								"",
							);
						}

						const testResponse = await fetch(
							"https://" + form.elements.domain.value + "/setup/statusnook",
							{method: "POST", mode: "cors"}
						);

						if (!testResponse.ok) {
							alert.classList.add("alert--success");
							alert.innerHTML = successMsg;
							alert2.innerHTML = infoMsg;
							[...form.querySelectorAll("label, button")].forEach((v) => {
								v.style.display = "none";
							});
							form.querySelector(".auth-dialog-continue").style.display = "block";
							return;
						}

						if (!testResponse.headers.get("X-Statusnook-Setup")) {
							alert.classList.add("alert--success");
							alert.innerHTML = successMsg;
							alert2.innerHTML = infoMsg;
							[...form.querySelectorAll("label, button")].forEach((v) => {
								v.style.display = "none";
							});
							form.querySelector(".auth-dialog-continue").style.display = "block";
							return;
						}

						return true;
					} catch(e) {
						if (Object.keys(e).length === 0) {
							alert.classList.add("alert--success");
							alert.innerHTML = successMsg;
							alert2.innerHTML = infoMsg;
							[...form.querySelectorAll("label, button")].forEach((v) => {
								v.style.display = "none";
							});
							form.querySelector(".auth-dialog-continue").style.display = "block";
						}
						return;
					} finally {
						form.classList.remove("htmx-request");
					}
				}

				document.addEventListener('htmx:afterRequest', async function(evt) {
					const form = document.querySelector("form");
					const dev = {{.DEV}};
					
					if (evt.detail.pathInfo.responsePath === "/setup/domain" && evt.detail.successful) {
						if (dev || await browserReachabilityTest()) {
							window.location.href = window.location.protocol + "//" + 
								form.elements.domain.value + "/setup/account";
						}
					}
				});
			</script>
		{{end}}
	`

	tmpl, err := parseTmpl("getSetupDomain", markup)
	if err != nil {
		log.Printf("getSetupDomain.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	prefillURLText := ""

	prefillURL, err := url.ParseRequestURI("http://" + r.Host)
	if err != nil {
		log.Printf("getSetupDomain.ParseRequestURI: %s", err)
		return
	}

	prefillIP := net.ParseIP(prefillURL.Hostname())
	if prefillIP.String() == "<nil>" {
		prefillURLText = prefillURL.Hostname()
	}

	dev := "false"
	if BUILD == "dev" {
		dev = "true"
	}

	err = tmpl.Execute(
		w,
		struct {
			DEV            template.JS
			SSL            string
			PrefillURLText string
			Ctx            map[string]string
		}{
			DEV:            template.JS(dev),
			SSL:            metaSSL,
			PrefillURLText: prefillURLText,
			Ctx:            map[string]string{},
		},
	)
	if err != nil {
		log.Printf("getSetupDomain.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func lookupDomain(domain string) (bool, error) {
	rootServers := []string{
		"a.root-servers.net",
		"b.root-servers.net",
		"c.root-servers.net",
		"d.root-servers.net",
		"e.root-servers.net",
		"f.root-servers.net",
		"g.root-servers.net",
		"h.root-servers.net",
		"i.root-servers.net",
		"j.root-servers.net",
		"k.root-servers.net",
		"l.root-servers.net",
		"m.root-servers.net",
	}

	rootNS := rootServers[mathRand.Intn(len(rootServers))]
	c := &dns.Client{}
	m := &dns.Msg{}
	m.SetQuestion(dns.Fqdn(domain), dns.TypeA)
	m.SetEdns0(4096, false)
	r, _, err := c.Exchange(m, rootNS+":53")
	if err != nil {
		return false, fmt.Errorf("lookupDomain.rootNS %s %s: %w", domain, rootNS, err)
	}
	if r.Rcode != dns.RcodeSuccess {
		return false, nil
	}

	authorityNS := r.Ns[mathRand.Intn(len(r.Ns))].(*dns.NS).Ns
	m = &dns.Msg{}
	m.SetQuestion(dns.Fqdn(domain), dns.TypeA)
	m.SetEdns0(4096, false)
	r, _, err = c.Exchange(m, authorityNS+":53")
	if err != nil {
		return false, fmt.Errorf("lookupDomain.authorityNS %s %s: %w", domain, authorityNS, err)
	}
	if r.Rcode != dns.RcodeSuccess {
		return false, nil
	}

	domainNS := r.Ns[mathRand.Intn(len(r.Ns))].(*dns.NS).Ns
	m = &dns.Msg{}
	m.SetQuestion(dns.Fqdn(domain), dns.TypeA)
	m.SetEdns0(4096, false)
	r, _, err = c.Exchange(m, domainNS+":53")
	if err != nil {
		return false, fmt.Errorf("lookupDomain.domainNS %s %s: %w", domain, domainNS, err)
	}
	if r.Rcode != dns.RcodeSuccess {
		return false, nil
	}

	return len(r.Answer) > 0, nil
}

var acmeProblemTypeMessages = map[string]string{
	acme.ProblemTypeDNS:                "Let's Encrypt can't find your domain's DNS record, verify it exists and then retry",
	acme.ProblemTypeConnection:         "Let's Encrypt could not reach your server, ensure your server is publicly accessible on ports 80 and 443, then try again",
	acme.ProblemTypeRejectedIdentifier: "Let's Encrypt will not issue certificates for this domain",
}

func postSetupDomain(w http.ResponseWriter, r *http.Request) {
	domainParam := r.PostFormValue("domain")
	if domainParam == "" {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert domain-alert" hx-swap-oob="true">
				Domain is required
			</div>
		`))
		return
	}

	domain, err := url.ParseRequestURI("https://" + domainParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert domain-alert" hx-swap-oob="true">
				Domain is invalid
			</div>
		`))
		return
	}

	hostname := domain.Hostname()
	if BUILD == "dev" || metaSSL == "false" {
		hostname = domain.Host
	}

	if BUILD == "release" && metaSSL == "true" {
		found, err := lookupDomain(hostname)
		if err != nil {
			log.Printf("postSetupDomain.lookupDomain: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(`
				<div id="alert" class="alert domain-alert" hx-swap-oob="true">
					An unhandled error occurred
				</div>
			`))
			return
		}

		if !found {
			w.WriteHeader(http.StatusBadRequest)
			w.Write([]byte(`
				<div id="alert" class="alert domain-alert" hx-swap-oob="true">
					<span>
						We didn't find your domain's A record, verify it exists and then retry
					</span>

					<span>
						If your domain and A record is correct, you might need to wait a few minutes before retrying
					</span>
				</div>

				<div id="skip-domain-setup" class="skip-domain-setup" hx-swap-oob="true">
					<p>We can also monitor things in the background and redirect you when your domain is ready</p>
					<form onsubmit="onSubmitSkipDomain(this);" hx-post="/setup/skip-domain" hx-swap="none">
						<input name="domain" type="hidden">
						<button>Skip ahead</button>
					</form>

					<script>
						function onSubmitSkipDomain(form) {
							const domain = document.querySelector(".setup-domain").elements.domain.value;
							form.elements.domain.value = domain;
						}
					</script>
				</div>
			`))
			return
		}

		err = certmagic.ManageSync(r.Context(), []string{hostname})
		if err != nil {
			var acmeProblem acme.Problem
			if errors.As(err, &acmeProblem) {
				if msg, ok := acmeProblemTypeMessages[acmeProblem.Type]; ok {
					w.WriteHeader(http.StatusBadRequest)
					w.Write([]byte(
						fmt.Sprintf(`
							<div id="alert" class="alert domain-alert" hx-swap-oob="true">
								%s
							</div>
						`,
							msg,
						),
					))
					return
				}

				w.WriteHeader(http.StatusBadRequest)
				w.Write([]byte(
					fmt.Sprintf(`
						<div id="alert" class="alert domain-alert" hx-swap-oob="true">
							An unhandled error occurred %s
						</div>
						`,
						acmeProblem.Type,
					),
				))
				return
			}

			log.Printf("postSetupDomain.ManageSync: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte(`
				<div id="alert" class="alert domain-alert" hx-swap-oob="true">
					An unexpected error occurred
				</div>
			`))
			return
		}
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postSetupDomain.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updateMetaValue(tx, "domain", hostname)
	if err != nil {
		log.Printf("postSetupDomain.updateMetaValueName: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMetaValue(tx, "setup", "account")
	if err != nil {
		log.Printf("postSetupDomain.updateMetaValueSetup: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err := tx.Commit(); err != nil {
		log.Printf("postSetupDomain.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	metaSetup = "account"
	metaDomain = hostname

	if BUILD == "dev" || metaSSL == "false" {
		w.Header().Add("HX-Location", "/setup/account")
	}
}

func postSetupDomainSkip(w http.ResponseWriter, r *http.Request) {
	domainParam := r.PostFormValue("domain")
	if domainParam == "" {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	domain, err := url.ParseRequestURI("https://" + domainParam)
	if err != nil {
		w.WriteHeader(http.StatusBadRequest)
		return
	}

	hostname := domain.Hostname()

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postSetupDomainSkip.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updateMetaValue(tx, "unconfirmedDomain", hostname)
	if err != nil {
		log.Printf("postSetupDomainSkip.updateMetaValueName: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMetaValue(tx, "setup", "account")
	if err != nil {
		log.Printf("postSetupDomainSkip.updateMetaValueSetup: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err := tx.Commit(); err != nil {
		log.Printf("postSetupDomainSkip.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	metaSetup = "account"
	metaUnconfirmedDomain = hostname

	appWg.Add(1)
	go monitorUnconfirmedDomainLoop(appCtx, &appWg)

	w.Header().Add("HX-Location", "/setup/account")
}

func getSetupAccount(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Create an admin user - Statusnook Setup{{end}}
		{{define "body"}}
			<div class="auth-dialog-container">
				<div class="auth-dialog">
					<div>
						<div>
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path d="M10 8a3 3 0 100-6 3 3 0 000 6zM3.465 14.493a1.23 1.23 0 00.41 1.412A9.957 9.957 0 0010 18c2.31 0 4.438-.784 6.131-2.1.43-.333.604-.903.408-1.41a7.002 7.002 0 00-13.074.003z" />
					  		</svg>			
						</div>
						<h1>Create an admin user</h1>
					</div>
					<form hx-post hx-swap="none">
						<div id="alert" class="alert"></div>
						<label>
							Username
							<input name="username" required>
						</label>

						<label>
							Password
							<input name="password" type="password" required>
						</label>
					
						<label>
							Confirm password
							<input name="password-confirmation" type="password" required>
						</label>

						<button>Confirm</button>
					</form>
				</div>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getSetupAccount", markup)
	if err != nil {
		log.Printf("getSetup.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(w, nil)
	if err != nil {
		log.Printf("getSetup.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func logout(w http.ResponseWriter, r *http.Request) {
	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("logout.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	sessionToken, err := r.Cookie("session")
	if err != nil {
		w.WriteHeader(http.StatusUnauthorized)
		return
	}

	if err = deleteSession(tx, sessionToken.Value); err != nil {
		log.Printf("logout.deleteSession: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("logout.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	http.SetCookie(
		w,
		&http.Cookie{
			Name:   "session",
			MaxAge: -1,
		},
	)

	w.Header().Add("HX-Location", "/")
}

func createUser(tx *sql.Tx, username string, pwHash string) (int, error) {
	const query = `
		insert into user(username, password) values(?, ?) returning id
	`

	userID := 0
	row := tx.QueryRow(query, username, pwHash)
	err := row.Scan(&userID)
	if err != nil {
		return userID, fmt.Errorf("createUser.Scan: %w", err)
	}

	return userID, nil
}

func editUserUsername(tx *sql.Tx, id int, username string) error {
	const query = `
		update user set username = ? where id = ?
	`

	_, err := tx.Exec(query, username, id)
	if err != nil {
		return fmt.Errorf("editUserUsername.Exec: %w", err)
	}

	return nil
}

func editUser(tx *sql.Tx, id int, username string, pwHash string) error {
	const query = `
		update user set username = ?, password = ? where id = ?
	`

	_, err := tx.Exec(query, username, pwHash, id)
	if err != nil {
		return fmt.Errorf("editUser.Exec: %w", err)
	}

	return nil
}

func deleteUserByID(tx *sql.Tx, id int) error {
	const query = `
		delete from user where id = ?
	`

	_, err := tx.Exec(query, id)
	if err != nil {
		return fmt.Errorf("deleteUserByID.Exec: %w", err)
	}

	return nil
}

func postSetupAccount(w http.ResponseWriter, r *http.Request) {
	username := r.PostFormValue("username")
	if username == "" {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Username is required
			</div>
		`))
		return
	}

	password := r.PostFormValue("password")
	passwordConfirmation := r.PostFormValue("password-confirmation")

	if password != passwordConfirmation {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Passwords do not match
			</div>
		`))
		return
	}

	if len(password) < 8 {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Password must contain at least 8 characters
			</div>
		`))
		return
	}

	pwHash, err := bcrypt.GenerateFromPassword([]byte(password), bcrypt.DefaultCost)
	if err != nil {
		log.Printf("postSetup.GenerateFromPassword: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postSetup.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	userID, err := createUser(tx, username, string(pwHash))
	if err != nil {
		log.Printf("postSetup.createUser: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	tokenBytes := make([]byte, 32)
	_, err = rand.Read(tokenBytes)
	if err != nil {
		log.Printf("postSetup.Read: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	csrfTokenBytes := make([]byte, 32)
	_, err = rand.Read(csrfTokenBytes)
	if err != nil {
		log.Printf("postSetup.Read2: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	token := base64.StdEncoding.EncodeToString(tokenBytes)
	csrfToken := base64.StdEncoding.EncodeToString(csrfTokenBytes)

	err = createSession(tx, token, csrfToken, userID)
	if err != nil {
		log.Printf("postSetup.createSession: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMetaValue(tx, "setup", "name")
	if err != nil {
		log.Printf("postSetup.updateMetaValue: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postSetup.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	metaSetup = "name"

	http.SetCookie(
		w,
		&http.Cookie{
			Name:     "session",
			Value:    token,
			Path:     "/",
			Expires:  time.Now().UTC().Add(time.Hour * 876600),
			Secure:   BUILD == "release",
			HttpOnly: true,
			SameSite: http.SameSiteLaxMode,
		},
	)

	w.Header().Add("HX-Location", "/setup/name")
}

func getSetupName(w http.ResponseWriter, r *http.Request) {
	const markup = `
		{{define "title"}}Name your nook - Statusnook Setup{{end}}
		{{define "body"}}
			<div class="auth-dialog-container">
				<div class="auth-dialog">
					<div>
						<div>
							<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
								<path fill-rule="evenodd" d="M4.5 2A2.5 2.5 0 0 0 2 4.5v3.879a2.5 2.5 0 0 0 .732 1.767l7.5 7.5a2.5 2.5 0 0 0 3.536 0l3.878-3.878a2.5 2.5 0 0 0 0-3.536l-7.5-7.5A2.5 2.5 0 0 0 8.38 2H4.5ZM5 6a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z" clip-rule="evenodd" />
							</svg>
						</div>
						<h1>Name your nook</h1>
					</div>
					<div style="margin-bottom: 6.0rem;">
						<p style="text-align: center;">This name will be displayed on your status page</p>
					</div>
					<form hx-post hx-swap="none">
						<div id="alert" class="alert" hx-swap-oob></div>
						<label>
							Name
							<input name="name" type="text" placeholder="Statusnook" required>
						</label>

						<button>Confirm</button>
					</form>
				</div>
			</div>
		{{end}}
	`

	tmpl, err := parseTmpl("getSetupName", markup)
	if err != nil {
		log.Printf("getSetup.parseTmpl: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = tmpl.Execute(w, nil)
	if err != nil {
		log.Printf("getSetup.Execute: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
}

func postSetupName(w http.ResponseWriter, r *http.Request) {
	name := r.PostFormValue("name")
	if name == "" {
		w.WriteHeader(http.StatusBadRequest)
		w.Write([]byte(`
			<div id="alert" class="alert" hx-swap-oob="true">
				Name is required
			</div>
		`))
		return
	}

	tx, err := rwDB.Begin()
	if err != nil {
		log.Printf("postSetupName.Begin: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	defer tx.Rollback()

	err = updateMetaValue(tx, "name", name)
	if err != nil {
		log.Printf("postSetupName.updateMetaValueName: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	err = updateMetaValue(tx, "setup", "done")
	if err != nil {
		log.Printf("postSetupName.updateMetaValueSetup: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	if err = tx.Commit(); err != nil {
		log.Printf("postSetupName.Commit: %s", err)
		w.WriteHeader(http.StatusInternalServerError)
		return
	}

	metaName = name
	metaSetup = "done"

	w.Header().Add("HX-Location", "/")
}
