// Code generated by sqlc. DO NOT EDIT.
// versions:
//   sqlc v1.29.0
// source: migration.sql

package sqlc

import (
	"context"
	"time"
)

const getDatabaseVersion = `-- name: GetDatabaseVersion :one
SELECT
  version
FROM
  migration_tracker
ORDER BY
  version DESC
LIMIT 1
`

func (q *Queries) GetDatabaseVersion(ctx context.Context) (int32, error) {
	row := q.db.QueryRowContext(ctx, getDatabaseVersion)
	var version int32
	err := row.Scan(&version)
	return version, err
}

const getMigration = `-- name: GetMigration :one
SELECT
  migration_time
FROM
  migration_tracker
WHERE
  version = $1
`

func (q *Queries) GetMigration(ctx context.Context, version int32) (time.Time, error) {
	row := q.db.QueryRowContext(ctx, getMigration, version)
	var migration_time time.Time
	err := row.Scan(&migration_time)
	return migration_time, err
}

const setMigration = `-- name: SetMigration :exec
INSERT INTO
  migration_tracker (version, migration_time) 
VALUES ($1, $2)
`

type SetMigrationParams struct {
	Version       int32
	MigrationTime time.Time
}

func (q *Queries) SetMigration(ctx context.Context, arg SetMigrationParams) error {
	_, err := q.db.ExecContext(ctx, setMigration, arg.Version, arg.MigrationTime)
	return err
}
